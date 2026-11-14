-- Prove2me | solution 1 for OAI.PrimeDegreePackets.tsum_lintegral_weightedUnitOrbitMellinKernel_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T06:50:29.532849+00:00
-- url     : https://prove2.me/submissions/3add56c9-25bf-4e21-9ec8-df158421871b

import Mathlib
import Definitions.Def_DukePrimeDegree
import Definitions.Def_OAIQ244Duke036

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_IdealCoefficients
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
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


lemma realDirichletTerm_ofReal (f : ArithmeticFunction ℝ) (s : ℝ) (m : ℕ) :
    (realDirichletTerm f s m : ℂ) = LSeries.term (fun m => (f m : ℂ)) s m := by
  by_cases hm : m = 0
  · subst m
    simp [realDirichletTerm]
  · simp only [realDirichletTerm, ArithmeticFunction.coe_mk,LSeries.term_of_ne_zero hm,
      Complex.ofReal_div, Complex.ofReal_cpow (Nat.cast_nonneg m),Complex.ofReal_natCast]

lemma idealCoefficient_real_summable {s : ℝ} (hs : 1 < s) :
    Summable (realDirichletTerm (idealCoefficientReal K) s) := by
  apply Complex.summable_ofReal.mp
  simp_rw [realDirichletTerm_ofReal]
  exact idealCoefficient_LSeriesSummable K (by simpa using hs)

lemma idealCoefficient_LSeries_eq (s : ℂ) :
    LSeries (fun m => (idealCoefficientReal K m : ℂ)) s = NumberField.dedekindZeta K s := by
  apply LSeries_congr _ s
  intro m hm
  simp only [idealCoefficientReal,ArithmeticFunction.coe_mk,idealCoefficient_pos K m hm,
    Complex.ofReal_natCast]

 
lemma idealDirichlet_eq_dedekindZeta (s : ℝ) :
    ((∑'m, realDirichletTerm (idealCoefficientReal K) s m : ℝ) : ℂ) =
      NumberField.dedekindZeta K s := by
  rw [Complex.ofReal_tsum, ←idealCoefficient_LSeries_eq]
  apply tsum_congr
  intro m
  exact realDirichletTerm_ofReal _ _ _

end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_MangoldtBounds
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
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

open scoped ArithmeticFunction.vonMangoldt


lemma realDirichletTerm_nonneg {f : ArithmeticFunction ℝ}
    (hf0 : ∀m, 0 ≤ f m) (s : ℝ) (m : ℕ) : 0 ≤ realDirichletTerm f s m := by
  exact div_nonneg (hf0 m) (Real.rpow_nonneg (Nat.cast_nonneg m) s)

end PrimeDegreePackets


end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_LocalEuler
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
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
open NumberField
open scoped BigOperators ENNReal nonZeroDivisors

lemma integralIdeal_norm_tsum {K : Type*} [Field K] [NumberField K] (F : ℕ → ℝ≥0∞) :
    (∑' I : {J : Ideal (𝓞 K) // J ≠ ⊥}, F (Ideal.absNorm I.1)) =
      ∑' m : ℕ, (idealCoefficient K m : ℝ≥0∞) * F m := by
  classical
  rw [← ENNReal.tsum_fiberwise (fun I : {J : Ideal (𝓞 K) // J ≠ ⊥} => F (Ideal.absNorm I.1))
    (fun I => Ideal.absNorm I.1)]
  apply tsum_congr
  intro m
  change (∑' I : {I : {J : Ideal (𝓞 K) // J ≠ ⊥} // Ideal.absNorm I.1 = m},
    F (Ideal.absNorm I.1.1)) = _
  have hf : (fun I : {I : {J : Ideal (𝓞 K) // J ≠ ⊥} // Ideal.absNorm I.1 = m} =>
    F (Ideal.absNorm I.1.1)) = fun _ => F m := by funext I; rw [I.2]
  rw [hf]
  by_cases hm : m = 0
  · subst m
    have : IsEmpty {I : {J : Ideal (𝓞 K) // J ≠ ⊥} // Ideal.absNorm I.1 = 0} :=
      ⟨fun I => I.1.2 (Ideal.absNorm_eq_zero_iff.mp I.2)⟩
    simp
  · rw [← (nonzeroIdealNormFiberEquiv (K := K) m hm).symm.tsum_eq]
    have : Finite {I : Ideal (𝓞 K) // Ideal.absNorm I = m} :=
      (Ideal.finite_setOfPred_absNorm_eq m).to_subtype
    let : Fintype {I : Ideal (𝓞 K) // Ideal.absNorm I = m} := Fintype.ofFinite _
    rw [tsum_fintype, Finset.sum_const, nsmul_eq_mul, idealCoefficient_pos K m hm,
      Nat.card_eq_fintype_card]
    rfl

end PrimeDegreePackets


namespace PrimeDegreePackets
open NumberField Finset
open scoped BigOperators ENNReal nonZeroDivisors

lemma dedekindZeta_real_eq_terms (K : Type*) [Field K] [NumberField K] (s : ℝ) :
    (NumberField.dedekindZeta K s).re =
      ∑' m : ℕ, realDirichletTerm (idealCoefficientReal K) s m := by
  simpa only [Complex.ofReal_re] using
    (congrArg Complex.re (idealDirichlet_eq_dedekindZeta K s)).symm

end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_ZetaResidues
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationPreservesVolume _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.diagonalLogAction_continuous _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.OAI.PrimeDegreePackets.periodSubmodule_addSubgroup_discrete _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupLocallyCompactSpace _root_.finiteLocalUnitsOpen _root_.ideleGroupLocallyCompactSpace _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupLocallyCompactSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.OAI.PrimeDegreePackets.orbitQuotientMap_mk _root_.infinitePlace_mult_smul
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
open Filter Set Topology NumberField

open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
namespace PrimeDegreePackets

open scoped NumberField nonZeroDivisors



open scoped Pointwise



open FractionalIdeal



lemma orderedUnitLog_ker
    {d : ℕ} {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) :
    (orderedUnitLog σ).ker = (NumberField.Units.torsion K).toAddSubgroup := by
  rw [← NumberField.Units.dirichletUnitTheorem.logEmbedding_ker]
  ext u
  change orderedLogCoordinatesEquiv σ (NumberField.Units.logEmbedding K u) = 0 ↔ _
  exact EmbeddingLike.map_eq_zero_iff



theorem tsum_comp_surjective_addHom {A B : Type*} [AddGroup A] [AddGroup B]
    (additiveMap : A →+ B) (hφ : Function.Surjective additiveMap) [Finite additiveMap.ker]
    (f : B → ℝ≥0∞) :
    (∑' a, f (additiveMap a)) = (Nat.card additiveMap.ker : ℝ≥0∞) * ∑' b, f b := by
  rw [← ENNReal.tsum_fiberwise (fun a => f (additiveMap a)) additiveMap,← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro b
  let e := AddMonoidHom.fiberEquivKerOfSurjective hφ b
  let := Fintype.ofFinite additiveMap.ker
  let := Fintype.ofEquiv additiveMap.ker e.symm
  calc
    (∑' a : additiveMap ⁻¹' {b}, f (additiveMap a)) = ∑' _a : additiveMap ⁻¹' {b}, f b := by
      apply tsum_congr
      intro a
      rw [show additiveMap a = b from a.property]
    _ = (Nat.card additiveMap.ker : ℝ≥0∞) * f b := by
      rw [tsum_fintype,Finset.sum_const,nsmul_eq_mul,Finset.card_univ,
        ← Nat.card_eq_fintype_card,Nat.card_congr e]

 

theorem lintegral_tsum_addHom_fundamentalDomain {d : ℕ} {A : Type*} [AddGroup A]
    (L : Submodule ℤ (Fin d → ℝ)) [Countable L]
    (additiveMap : A →+ L) (hφ : Function.Surjective additiveMap) [Finite additiveMap.ker]
    {t : Set (Fin d → ℝ)} (ht : IsAddFundamentalDomain L t volume)
    (f : (Fin d → ℝ) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ u in t, ∑' a, f ((additiveMap a : Fin d → ℝ)+u)) =
      (Nat.card additiveMap.ker : ℝ≥0∞) * ∫⁻ v, f v := by
  have he (u : Fin d → ℝ) : (∑' a, f ((additiveMap a : Fin d → ℝ)+u)) =
      (Nat.card additiveMap.ker : ℝ≥0∞) * ∑' p : L, f ((p : Fin d → ℝ)+u) :=
    tsum_comp_surjective_addHom additiveMap hφ (fun p => f ((p : Fin d → ℝ)+u))
  have : VAddInvariantMeasure L (Fin d → ℝ) volume :=
    (inferInstance : VAddInvariantMeasure L.toAddSubgroup (Fin d → ℝ) volume)
  simp_rw [he]
  rw [lintegral_const_mul _ (by fun_prop)]
  congr 1
  rw [ht.lintegral_eq_tsum'' f]
  exact lintegral_tsum (fun p => (hf.comp (measurable_const.add measurable_id)).aemeasurable)



lemma logFlowWeights_add {d : ℕ} (u t : LogCoordinates d) :
    logFlowWeights (u+t) = logFlowWeights u * logFlowWeights t := by
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;>
    simp [logFlowWeights,Real.exp_add,Finset.sum_add_distrib,mul_comm]

lemma continuous_logFlowWeights {d : ℕ} : Continuous (@logFlowWeights d) := by
  apply continuous_pi
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp only [logFlowWeights,Fin.snoc_last,Fin.snoc_castSucc]
  · fun_prop
  · fun_prop

lemma logFlowWeights_orderedUnitLog {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K) (z : (𝓞 K)ˣ) :
    logFlowWeights (orderedUnitLog σ (Additive.ofMul z)) = fun i => |σ i (z : K)| := by
  have h := diagonalFlow_abs_orderedUnitLog σ z
  have H (i : Fin (d+1)) := congrArg (fun A : Matrix (Fin (d+1)) (Fin (d+1)) ℝ => A i i) h
  funext i
  exact by simpa only [diagonalFlow,logFlowWeights,Matrix.diagonal_apply_eq] using H i



lemma orderedUnitLogOnto_ker {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K) :
    (orderedUnitLogOnto σ).ker = (NumberField.Units.torsion K).toAddSubgroup := by
  rw [orderedUnitLogOnto,AddMonoidHom.ker_codRestrict,orderedUnitLog_ker]

lemma tsum_integralFractionalIdeals (K : Type*) [Field K] [NumberField K]
    (F : FractionalIdeal (𝓞 K)⁰ K → ℝ≥0∞) :
    (∑' J : integralFractionalIdeals K, F J.1) = ∑' J : {J : Ideal (𝓞 K) // J ≠ ⊥}, F J.1 :=
  ((integralFractionalIdealsEquiv K).tsum_eq (fun J => F J.1)).symm



lemma prod_orderedEmbeddings {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (σ : OrderedEmbeddings n K) (hn : Module.finrank ℚ K = n) (a : K) :
    ∏ i, σ i a = (Algebra.norm ℚ a : ℝ) := by
  apply Complex.ofReal_injective
  have h := Algebra.norm_eq_prod_embeddings ℚ ℂ a
  rw [← (orderedComplexEmbeddings σ hn).prod_comp] at h
  change (algebraMap ℚ ℂ) (Algebra.norm ℚ a) = ∏ i, Complex.ofReal (σ i a) at h
  rw [← Complex.ofReal_prod] at h
  change (Algebra.norm ℚ a : ℂ) = _ at h
  simpa only [Complex.ofReal_ratCast] using h.symm

lemma prod_abs_orderedEmbeddings {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (σ : OrderedEmbeddings n K) (hn : Module.finrank ℚ K = n) (a : K) :
    ∏ i, |σ i a| = |(Algebra.norm ℚ a : ℝ)| := by
  rw [← Finset.abs_prod,prod_orderedEmbeddings σ hn]

lemma fractionalIdeal_absNorm_pos {K : Type*} [Field K] [NumberField K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    0 < (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ) := by
  exact_mod_cast lt_of_le_of_ne (FractionalIdeal.absNorm_nonneg I.1)
    (fun h => I.ne_zero (FractionalIdeal.absNorm_eq_zero_iff.mp h.symm))

end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_ThetaTails
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.infinitePlace_mult_smul
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
open NumberField Finset
open NumberField Filter Set Topology
open MeasureTheory ProbabilityTheory Matrix
open scoped Classical BigOperators ENNReal
open MeasureTheory Set Filter Topology Module
open scoped BigOperators SchwartzMap
open MeasureTheory Set Filter Topology Module WithLp
open scoped BigOperators SchwartzMap ZeroAtInfty
open scoped FourierTransform
open scoped BigOperators SchwartzMap FourierTransform
open scoped BigOperators FourierTransform
open MeasureTheory Set Filter Topology Module WithLp Asymptotics
open Module WithLp MeasureTheory
open scoped BigOperators Matrix
open Module MeasureTheory


namespace PrimeDegreePackets
open ThetaConstruction


lemma restoredLogCoordinates_exp {d : ℕ} (u : LogCoordinates d) (i : Fin (d+1)) :
    Real.exp (restoredLogCoordinates u i) = logFlowWeights u i := by
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [restoredLogCoordinates,logFlowWeights]

lemma restoredLogCoordinates_continuous {d : ℕ} (i : Fin (d+1)) :
    Continuous (fun u : LogCoordinates d => restoredLogCoordinates u i) := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [restoredLogCoordinates,Fin.snoc_last]
    fun_prop
  · simp only [restoredLogCoordinates,Fin.snoc_castSucc]
    exact continuous_apply j

end PrimeDegreePackets


end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_LatticeDuality
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.infinitePlace_mult_smul
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
open NumberField Finset
open NumberField Filter Set Topology
open MeasureTheory ProbabilityTheory Matrix
open scoped Classical BigOperators ENNReal
open MeasureTheory Set Filter Topology Module
open scoped BigOperators SchwartzMap
open MeasureTheory Set Filter Topology Module WithLp
open scoped BigOperators SchwartzMap ZeroAtInfty
open scoped FourierTransform
open scoped BigOperators SchwartzMap FourierTransform
open scoped BigOperators FourierTransform
open MeasureTheory Set Filter Topology Module WithLp Asymptotics
open Module WithLp MeasureTheory
open scoped BigOperators Matrix
open Module MeasureTheory


namespace PrimeDegreePackets
open ThetaConstruction

lemma restoredLogCoordinates_sum {d : ℕ} (u : LogCoordinates d) :
    ∑ i, restoredLogCoordinates u i = 0 := by
  simp [restoredLogCoordinates,Fin.sum_univ_castSucc]

end PrimeDegreePackets


open MeasureTheory Module WithLp

open scoped BigOperators NumberField nonZeroDivisors ENNReal
namespace PrimeDegreePackets
open ThetaConstruction


lemma arithmeticFlowGaussian_measurable {d : ℕ} {K : Type*} [Field K]
    (σ : OrderedEmbeddings (d+1) K) (a : K) (t : ℝ) :
    Measurable (arithmeticFlowGaussian σ a t) := by
  unfold arithmeticFlowGaussian
  apply Measurable.ennreal_ofReal
  apply Continuous.measurable
  apply Continuous.rexp
  apply Continuous.mul continuous_const
  apply continuous_finsetSum
  intro i _
  exact (((continuous_apply i).comp continuous_logFlowWeights).mul_const _).pow 2

lemma arithmeticFlowGaussian_unit_translate {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K)
    (a : K) (z : (𝓞 K)ˣ) (t : ℝ) (u : LogCoordinates d) :
    arithmeticFlowGaussian σ ((z:K)*a) t u =
      arithmeticFlowGaussian σ a t (orderedUnitLog σ (Additive.ofMul z)+u) := by
  unfold arithmeticFlowGaussian
  simp only [map_mul,logFlowWeights_add,logFlowWeights_orderedUnitLog]
  congr 3
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.mul_apply,mul_pow,sq_abs]
  ring



end PrimeDegreePackets


end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_ZeroReflection
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupLocallyCompactSpace _root_.finiteLocalUnitsOpen _root_.ideleGroupLocallyCompactSpace _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupLocallyCompactSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.infinitePlace_mult_smul
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
open NumberField Finset
open NumberField Filter Set Topology
open MeasureTheory ProbabilityTheory Matrix
open scoped Classical BigOperators ENNReal
open MeasureTheory Set Filter Topology Module
open scoped BigOperators SchwartzMap
open MeasureTheory Set Filter Topology Module WithLp
open scoped BigOperators SchwartzMap ZeroAtInfty
open scoped FourierTransform
open scoped BigOperators SchwartzMap FourierTransform
open scoped BigOperators FourierTransform
open MeasureTheory Set Filter Topology Module WithLp Asymptotics
open Module WithLp MeasureTheory
open scoped BigOperators Matrix
open Module MeasureTheory
open MeasureTheory Module WithLp
open scoped BigOperators NumberField nonZeroDivisors ENNReal
open Complex Set Metric Filter
open Complex Set Metric Filter MeromorphicOn
open scoped Topology ComplexConjugate
open MeasureTheory Set Filter


namespace PrimeDegreePackets.HeckeMellin

lemma lintegral_comp_pos_mul {c : ℝ} (hc : 0 < c) (f : ℝ → ℝ≥0∞) :
    (∫⁻ x, f (c*x)) = ENNReal.ofReal c⁻¹ * ∫⁻ x, f x := by
  have H := lintegral_image_eq_lintegral_abs_deriv_mul
    (s := Set.univ) (f := fun x : ℝ => c⁻¹*x) (f' := fun _ => c⁻¹)
    MeasurableSet.univ
    (fun x _ => by simpa using (hasDerivAt_id x).const_mul c⁻¹)
    (fun _ _ _ _ h => mul_left_cancel₀ (inv_ne_zero hc.ne') h)
    (fun x => f (c*x))
  have hi : (fun x : ℝ => c⁻¹*x) '' Set.univ = Set.univ := by
    ext y
    simp only [mem_image, mem_univ, true_and, iff_true]
    exact ⟨c*y, by simp [hc.ne']⟩
  simpa only [hi, Measure.restrict_univ, abs_of_pos (inv_pos.mpr hc),
    ← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] using H

lemma lintegral_snoc (d : ℕ) (f : (Fin (d+1) → ℝ) → ℝ≥0∞)
    (hf : Measurable f) :
    (∫⁻ u : Fin d → ℝ, ∫⁻ v : ℝ, f (Fin.snoc u v)) = ∫⁻ x, f x := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d+1) => ℝ) (Fin.last d)
  have he := (volume_preserving_piFinSuccAbove (fun _ : Fin (d+1) => ℝ) (Fin.last d)).symm
  have H := he.lintegral_comp (f := f) hf
  change (∫⁻ p : ℝ × (Fin d → ℝ), f (e.symm p)) = _ at H
  have hs (p : ℝ × (Fin d → ℝ)) : e.symm p = Fin.snoc p.2 p.1 := by
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;>
      simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply]
  simp_rw [hs] at H
  rw [Measure.volume_eq_prod, lintegral_prod _ (by fun_prop)] at H
  rw [lintegral_lintegral_swap (by fun_prop)] at H
  exact H


lemma continuous_coordinates (d : ℕ) :
    Continuous (fun p : (Fin d → ℝ) × ℝ => coordinates d p.1 p.2) := by
  apply continuous_pi
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i <;>
    simp only [coordinates, Fin.snoc_last, Fin.snoc_castSucc] <;> fun_prop

 
theorem lintegral_coordinates (d : ℕ) (f : (Fin (d+1) → ℝ) → ℝ≥0∞)
    (hf : Measurable f) :
    (∫⁻ v : ℝ, ∫⁻ u : Fin d → ℝ, f (coordinates d u v)) =
      ENNReal.ofReal (2/(d+1 : ℝ)) * ∫⁻ x, f x := by
  let c : ℝ := (d+1 : ℝ)/2
  have hc : 0 < c := by dsimp [c] <;> positivity
  have he (u : Fin d → ℝ) (v : ℝ) :
      coordinates d u v =
        Fin.snoc (u + (fun _ : Fin d => v/2)) (c*v - ∑ i, (u + (fun _ : Fin d => v/2)) i) := by
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [coordinates, Finset.sum_add_distrib, c]
      ring
    · simp [coordinates]
  calc
    _ = ∫⁻ v : ℝ, ∫⁻ u : Fin d → ℝ, f (Fin.snoc u (c*v - ∑ i, u i)) := by
      apply lintegral_congr
      intro v
      simp_rw [he]
      exact lintegral_add_right_eq_self (fun u : Fin d → ℝ =>
        f (Fin.snoc u (c*v - ∑ i, u i))) (fun _ => v/2)
    _ = ∫⁻ u : Fin d → ℝ, ∫⁻ v : ℝ, f (Fin.snoc u (c*v - ∑ i, u i)) := by
      apply lintegral_lintegral_swap
      apply Measurable.aemeasurable
      apply hf.comp
      apply measurable_pi_iff.mpr
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i <;>
        simp only [Fin.snoc_last, Fin.snoc_castSucc] <;> fun_prop
    _ = ∫⁻ u : Fin d → ℝ, ENNReal.ofReal c⁻¹ * ∫⁻ w : ℝ, f (Fin.snoc u w) := by
      apply lintegral_congr
      intro u
      rw [lintegral_comp_pos_mul hc (fun v => f (Fin.snoc u (v - ∑ i, u i)))]
      congr 1
      exact lintegral_sub_right_eq_self (fun w => f (Fin.snoc u w)) (∑ i, u i)
    _ = ENNReal.ofReal c⁻¹ * ∫⁻ x, f x := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_snoc d f hf]
    _ = _ := by congr 2; dsimp [c]; field_simp

 

theorem map_coordinates (d : ℕ) :
    Measure.map (fun p : ℝ × (Fin d → ℝ) => coordinates d p.2 p.1) volume =
      ENNReal.ofReal (2/(d+1 : ℝ)) • (volume : Measure (Fin (d+1) → ℝ)) := by
  apply Measure.ext_of_lintegral
  intro f hf
  have hc : Continuous (fun p : ℝ × (Fin d → ℝ) => coordinates d p.2 p.1) :=
    (continuous_coordinates d).comp continuous_swap
  have hfc : Measurable (fun p : ℝ × (Fin d → ℝ) => f (coordinates d p.2 p.1)) :=
    hf.comp hc.measurable
  rw [lintegral_map hf hc.measurable, lintegral_smul_measure,
    Measure.volume_eq_prod, lintegral_prod _ hfc.aemeasurable]
  exact lintegral_coordinates d f hf

lemma integral_coordinates {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (d : ℕ) (f : (Fin (d+1) → ℝ) → F) (hf : StronglyMeasurable f) :
    (∫ p : ℝ × (Fin d → ℝ), f (coordinates d p.2 p.1)) =
      (2/(d+1 : ℝ)) • ∫ x, f x := by
  have hc : Continuous (fun p : ℝ × (Fin d → ℝ) => coordinates d p.2 p.1) :=
    (continuous_coordinates d).comp continuous_swap
  rw [← integral_map hc.measurable.aemeasurable hf.aestronglyMeasurable,
    map_coordinates, integral_smul_measure, ENNReal.toReal_ofReal (by positivity)]

lemma integrable_coordinates {F : Type*} [NormedAddCommGroup F]
    (d : ℕ) (f : (Fin (d+1) → ℝ) → F) (hf : StronglyMeasurable f)
    (hI : Integrable f) :
    Integrable (fun p : ℝ × (Fin d → ℝ) => f (coordinates d p.2 p.1)) := by
  have hc : Continuous (fun p : ℝ × (Fin d → ℝ) => coordinates d p.2 p.1) :=
    (continuous_coordinates d).comp continuous_swap
  apply (integrable_map_measure hf.aestronglyMeasurable hc.measurable.aemeasurable).mp
  rw [map_coordinates]
  exact hI.smul_measure ENNReal.ofReal_ne_top

end PrimeDegreePackets.HeckeMellin


namespace PrimeDegreePackets.HeckeMellin


lemma logGammaKernel_eq (s : ℂ) (x : ℝ) :
    logGammaKernel s x = Real.exp x •
      ((Real.exp (-Real.exp x) : ℂ) * (Real.exp x : ℂ) ^ (s-1)) := by
  rw [Complex.real_smul, Complex.cpow_def_of_ne_zero
    (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero x)),
    ← Complex.ofReal_log (Real.exp_pos x).le, Real.log_exp]
  simp only [logGammaKernel, Complex.ofReal_exp, Complex.ofReal_neg]
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  ring

lemma integrable_logGammaKernel {s : ℂ} (hs : 0 < s.re) :
    Integrable (logGammaKernel s) := by
  have H := integrableOn_image_iff_integrableOn_abs_deriv_smul
    (s := Set.univ) (f := Real.exp) (f' := Real.exp) MeasurableSet.univ
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
    Real.exp_injective.injOn
    (fun t : ℝ => (Real.exp (-t) : ℂ) * (t : ℂ) ^ (s-1))
  simp only [Set.image_univ, Real.range_exp, abs_of_pos (Real.exp_pos _),
    ← logGammaKernel_eq, integrableOn_univ] at H
  exact H.mp (Complex.GammaIntegral_convergent hs)

lemma integral_logGammaKernel {s : ℂ} (hs : 0 < s.re) :
    (∫ x : ℝ, logGammaKernel s x) = Complex.Gamma s := by
  have H := integral_image_eq_integral_abs_deriv_smul
    (s := Set.univ) (f := Real.exp) (f' := Real.exp) MeasurableSet.univ
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
    Real.exp_injective.injOn
    (fun t : ℝ => (Real.exp (-t) : ℂ) * (t : ℂ) ^ (s-1))
  rw [Complex.Gamma_eq_integral hs, Complex.GammaIntegral]
  simpa only [Set.image_univ, Real.range_exp, abs_of_pos (Real.exp_pos _),
    ← logGammaKernel_eq, Measure.restrict_univ] using H.symm


lemma gaussianLogKernel_eq {r : ℝ} (hr : 0 < r) (s : ℂ) (x : ℝ) :
    gaussianLogKernel s r x = (r : ℂ) ^ (-(s/2)) *
      logGammaKernel (s/2) (2*x + Real.log r) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne'),
    ← Complex.ofReal_log hr.le, logGammaKernel, ← Complex.exp_add,
    Real.exp_add, Real.exp_log hr]
  simp only [gaussianLogKernel, Complex.ofReal_add, Complex.ofReal_mul,
    Complex.ofReal_ofNat]
  congr 1
  ring

lemma integrable_gaussianLogKernel {s : ℂ} (hs : 0 < s.re) {r : ℝ} (hr : 0 < r) :
    Integrable (gaussianLogKernel s r) := by
  have ha : 0 < (s/2).re := by simpa using half_pos hs
  have H := ((integrable_logGammaKernel ha).comp_add_right (Real.log r)).comp_mul_left'
    (R := (2 : ℝ)) (by norm_num)
  simpa only [← gaussianLogKernel_eq hr] using H.const_mul ((r : ℂ)^(-(s/2)))

lemma integral_gaussianLogKernel {s : ℂ} (hs : 0 < s.re) {r : ℝ} (hr : 0 < r) :
    (∫ x : ℝ, gaussianLogKernel s r x) =
      (1/2 : ℂ) * (r : ℂ) ^ (-(s/2)) * Complex.Gamma (s/2) := by
  have ha : 0 < (s/2).re := by simpa using half_pos hs
  simp_rw [gaussianLogKernel_eq hr]
  rw [integral_const_mul, Measure.integral_comp_mul_left
      (fun x => logGammaKernel (s/2) (x + Real.log r)) 2,
    integral_add_right_eq_self, integral_logGammaKernel ha]
  norm_num [Complex.real_smul]
  ring

lemma continuous_gaussianLogKernel (s : ℂ) (r : ℝ) :
    Continuous (gaussianLogKernel s r) := by
  unfold gaussianLogKernel
  fun_prop


lemma exp_two_mul (x : ℝ) : Real.exp (2*x) = (Real.exp x)^2 := by
  rw [show 2*x = x+x by ring, Real.exp_add, pow_two]

lemma scaled_cpow {r a : ℝ} (hr : 0 < r) (ha : a ≠ 0) (s : ℂ) :
    ((r*a^2 : ℝ) : ℂ)^(-(s/2)) = (r : ℂ)^(-(s/2)) * ((|a| : ℝ) : ℂ)^(-s) := by
  have hsq : 0 < a^2 := sq_pos_of_ne_zero ha
  have hab : 0 < |a| := abs_pos.mpr ha
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (mul_pos hr hsq).ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hab.ne'),
    ← Complex.exp_add, ← Complex.ofReal_log (mul_pos hr hsq).le,
    ← Complex.ofReal_log hr.le, ← Complex.ofReal_log hab.le,
    Real.log_mul hr.ne' (pow_ne_zero _ ha), Real.log_pow, Real.log_abs]
  push_cast
  congr 1
  ring

lemma gaussianLogKernel_scale (s : ℂ) (r a x : ℝ) :
    gaussianLogKernel s (r*a^2) x =
      Complex.exp (s*(x : ℂ) - (r*(a*Real.exp x)^2 : ℝ)) := by
  rw [gaussianLogKernel, exp_two_mul]
  congr 2
  push_cast
  ring

lemma prod_abs_cpow {ι : Type*} [Fintype ι] (a : ι → ℝ) (ha : ∀ i, a i ≠ 0) (s : ℂ) :
    (∏ i, ((|a i| : ℝ) : ℂ)^s) = ((∏ i, |a i| : ℝ) : ℂ)^s := by
  have hp : 0 < ∏ i, |a i| := Finset.prod_pos (fun i _ => abs_pos.mpr (ha i))
  have H (i : ι) : ((|a i| : ℝ) : ℂ)^s = Complex.exp ((Real.log |a i| : ℂ)*s) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr (ha i))),
      ← Complex.ofReal_log (abs_nonneg _)]
  simp_rw [H]
  rw [← Complex.exp_sum,
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hp.ne'),
    ← Complex.ofReal_log hp.le, Real.log_prod (fun i _ => abs_ne_zero.mpr (ha i)),
    Complex.ofReal_sum, Finset.sum_mul]

end PrimeDegreePackets.HeckeMellin


namespace PrimeDegreePackets.HeckeMellin

lemma coordinates_eq (d : ℕ) (u : LogCoordinates d) (v : ℝ) (i : Fin (d+1)) :
    coordinates d u v i = restoredLogCoordinates u i + v/2 := by
  refine Fin.lastCases ?_ (fun j => ?_) i <;>
    simp [coordinates, restoredLogCoordinates]

lemma sum_coordinates (d : ℕ) (u : LogCoordinates d) (v : ℝ) :
    ∑ i, coordinates d u v i = (d+1 : ℝ)*v/2 := by
  simp_rw [coordinates_eq]
  rw [Finset.sum_add_distrib, restoredLogCoordinates_sum]
  simp
  ring


lemma continuous_logEnergy {d : ℕ} (a : Fin (d+1) → ℝ) :
    Continuous (logEnergy a) := by
  unfold logEnergy
  exact continuous_finsetSum _ (fun i _ =>
    (continuous_const.mul (Real.continuous_exp.comp (restoredLogCoordinates_continuous i))).pow 2)

lemma gaussianLogKernel_coordinates {d : ℕ} (s : ℂ) (r : ℝ)
    (a : Fin (d+1) → ℝ) (p : ℝ × LogCoordinates d) :
    (∏ i, gaussianLogKernel s (r*(a i)^2) (coordinates d p.2 p.1 i)) =
      logRadialKernel s r a p := by
  simp_rw [gaussianLogKernel_scale]
  rw [← Complex.exp_sum]
  congr 1
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Complex.ofReal_sum,
    sum_coordinates, ← Complex.ofReal_sum]
  have HE : ∑ i, r*(a i*Real.exp (coordinates d p.2 p.1 i))^2 =
      r*Real.exp p.1*logEnergy a p.2 := by
    have H (i : Fin (d+1)) : r*(a i*Real.exp (coordinates d p.2 p.1 i))^2 =
        (r*Real.exp p.1)*(a i*Real.exp (restoredLogCoordinates p.2 i))^2 := by
      rw [coordinates_eq, Real.exp_add, mul_pow, mul_pow, ← exp_two_mul (p.1/2),
        show 2*(p.1/2) = p.1 by ring, mul_pow]
      ring
    simp_rw [H]
    rw [← Finset.mul_sum]
    rfl
  rw [HE]
  push_cast
  congr 1
  ring

lemma integrable_logRadialKernel {d : ℕ} {s : ℂ} (hs : 0 < s.re)
    {r : ℝ} (hr : 0 < r) (a : Fin (d+1) → ℝ) (ha : ∀ i, a i ≠ 0) :
    Integrable (logRadialKernel s r a) := by
  have hprod : Integrable (fun x : Fin (d+1) → ℝ => ∏ i, gaussianLogKernel s (r*(a i)^2) (x i)) :=
    Integrable.fintype_prod (fun i => integrable_gaussianLogKernel hs
      (mul_pos hr (sq_pos_of_ne_zero (ha i))))
  have hcont : Continuous (fun x : Fin (d+1) → ℝ => ∏ i, gaussianLogKernel s (r*(a i)^2) (x i)) := by
    apply continuous_finsetProd
    intro i _
    exact (continuous_gaussianLogKernel s _).comp (continuous_apply i)
  have H := integrable_coordinates d _ hcont.stronglyMeasurable hprod
  simpa only [gaussianLogKernel_coordinates] using H

 
theorem integral_logRadialKernel {d : ℕ} {s : ℂ} (hs : 0 < s.re)
    {r : ℝ} (hr : 0 < r) (a : Fin (d+1) → ℝ) (ha : ∀ i, a i ≠ 0) :
    (∫ p, logRadialKernel s r a p) =
      (2/(d+1 : ℂ)) *
        ((1/2 : ℂ)*(r : ℂ)^(-(s/2))*Complex.Gamma (s/2))^(d+1) *
        ((∏ i, |a i| : ℝ) : ℂ)^(-s) := by
  have hcont : Continuous (fun x : Fin (d+1) → ℝ => ∏ i, gaussianLogKernel s (r*(a i)^2) (x i)) := by
    apply continuous_finsetProd
    intro i _
    exact (continuous_gaussianLogKernel s _).comp (continuous_apply i)
  have H := integral_coordinates d _ hcont.stronglyMeasurable
  simp only [gaussianLogKernel_coordinates] at H
  rw [H, integral_fintype_prod_volume_eq_prod]
  simp_rw [integral_gaussianLogKernel hs (mul_pos hr (sq_pos_of_ne_zero (ha _))),
    scaled_cpow hr (ha _)]
  simp_rw [show ∀ i, (1/2 : ℂ)*((r : ℂ)^(-(s/2)) * ((|a i| : ℝ) : ℂ)^(-s)) *
      Complex.Gamma (s/2) =
        ((1/2 : ℂ)*(r : ℂ)^(-(s/2))*Complex.Gamma (s/2)) * ((|a i| : ℝ) : ℂ)^(-s)
      from fun i => by ring]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_fin, prod_abs_cpow a ha,
    Complex.real_smul]
  push_cast
  ring


lemma logRadialKernel_eq_radial {d : ℕ} (s : ℂ) (r : ℝ)
    (a : Fin (d+1) → ℝ) (v : ℝ) (u : LogCoordinates d) :
    logRadialKernel s r a (v,u) = Real.exp v • radialKernel s r a (Real.exp v) u := by
  rw [radialKernel, Complex.real_smul,
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero v)),
    ← Complex.ofReal_log (Real.exp_pos v).le, Real.log_exp, Complex.ofReal_exp,
    ← Complex.exp_add, ← Complex.exp_add]
  unfold logRadialKernel
  congr 1
  push_cast
  ring

lemma radialIntegral_log {d : ℕ} (s : ℂ) (r : ℝ)
    (a : Fin (d+1) → ℝ) (v : ℝ) :
    (∫ u, logRadialKernel s r a (v,u)) =
      Real.exp v • ∫ u, radialKernel s r a (Real.exp v) u := by
  simp_rw [logRadialKernel_eq_radial]
  exact integral_smul _ _



theorem integral_radialKernel {d : ℕ} {s : ℂ} (hs : 0 < s.re)
    {r : ℝ} (hr : 0 < r) (a : Fin (d+1) → ℝ) (ha : ∀ i, a i ≠ 0) :
    (∫ t in Ioi 0, ∫ u, radialKernel s r a t u) =
      (2/(d+1 : ℂ)) *
        ((1/2 : ℂ)*(r : ℂ)^(-(s/2))*Complex.Gamma (s/2))^(d+1) *
        ((∏ i, |a i| : ℝ) : ℂ)^(-s) := by
  have H := integral_image_eq_integral_abs_deriv_smul
    (s := Set.univ) (f := Real.exp) (f' := Real.exp) MeasurableSet.univ
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
    Real.exp_injective.injOn (fun t => ∫ u, radialKernel s r a t u)
  simp only [Set.image_univ, Real.range_exp, abs_of_pos (Real.exp_pos _),
    ← radialIntegral_log, Measure.restrict_univ] at H
  rw [H]
  have HI := integrable_logRadialKernel hs hr a ha
  rw [Measure.volume_eq_prod] at HI
  rw [← integral_prod _ HI, ← Measure.volume_eq_prod]
  exact integral_logRadialKernel hs hr a ha

end PrimeDegreePackets.HeckeMellin
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_RadialIntegrals
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.ValuationSubring.charP _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupLocallyCompactSpace _root_.finiteLocalUnitsOpen _root_.ideleGroupLocallyCompactSpace _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupLocallyCompactSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EmbeddingOrder.toRealOrder_apply _root_.infinitePlace_mult_smul
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
open NumberField Finset
open NumberField Filter Set Topology
open MeasureTheory ProbabilityTheory Matrix
open scoped Classical BigOperators ENNReal
open MeasureTheory Set Filter Topology Module
open scoped BigOperators SchwartzMap
open MeasureTheory Set Filter Topology Module WithLp
open scoped BigOperators SchwartzMap ZeroAtInfty
open scoped FourierTransform
open scoped BigOperators SchwartzMap FourierTransform
open scoped BigOperators FourierTransform
open MeasureTheory Set Filter Topology Module WithLp Asymptotics
open Module WithLp MeasureTheory
open scoped BigOperators Matrix
open Module MeasureTheory
open MeasureTheory Module WithLp
open scoped BigOperators NumberField nonZeroDivisors ENNReal
open Complex Set Metric Filter
open Complex Set Metric Filter MeromorphicOn
open scoped Topology ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology
namespace PrimeDegreePackets.HeckeMellin

lemma measurable_radialKernel {d : ℕ} (s : ℂ) (r : ℝ) (a : Fin (d+1) → ℝ) :
    Measurable (fun p : ℝ × LogCoordinates d => radialKernel s r a p.1 p.2) := by
  unfold radialKernel
  have he := continuous_logEnergy a
  fun_prop

lemma lintegral_exp_product {E : Type*} [MeasureSpace E] [SFinite (volume : Measure E)]
    (f : ℝ × E → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ p : ℝ × E, ENNReal.ofReal (Real.exp p.1) * f (Real.exp p.1,p.2)) =
      ∫⁻ t in Ioi 0, ∫⁻ u, f (t,u) := by
  have H := lintegral_image_eq_lintegral_abs_deriv_mul
    (s := Set.univ) (f := Real.exp) (f' := Real.exp) MeasurableSet.univ
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
    Real.exp_injective.injOn (fun t => ∫⁻ u, f (t,u))
  simp only [Set.image_univ, Real.range_exp, abs_of_pos (Real.exp_pos _),
    Measure.restrict_univ] at H
  rw [H, Measure.volume_eq_prod, lintegral_prod _ (by fun_prop)]
  apply lintegral_congr
  intro v
  simpa only using lintegral_const_mul' (ENNReal.ofReal (Real.exp v))
    (fun u : E => f (Real.exp v,u)) ENNReal.ofReal_ne_top

lemma lintegral_norm_radialKernel {d : ℕ} (s : ℂ) (r : ℝ) (a : Fin (d+1) → ℝ) :
    (∫⁻ t in Ioi 0, ∫⁻ u, ENNReal.ofReal ‖radialKernel s r a t u‖) =
      ∫⁻ p, ENNReal.ofReal ‖logRadialKernel s r a p‖ := by
  rw [← lintegral_exp_product _ ((measurable_radialKernel s r a).norm.ennreal_ofReal)]
  apply lintegral_congr
  intro p
  rw [logRadialKernel_eq_radial, norm_smul, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), ENNReal.ofReal_mul (Real.exp_pos _).le]

 

theorem integrable_radialKernel_product {d : ℕ} {s : ℂ} (hs : 0 < s.re)
    {r : ℝ} (hr : 0 < r) (a : Fin (d+1) → ℝ) (ha : ∀ i, a i ≠ 0) :
    Integrable (fun p : ℝ × LogCoordinates d => radialKernel s r a p.1 p.2)
      ((volume.restrict (Ioi 0)).prod volume) := by
  refine ⟨(measurable_radialKernel s r a).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  rw [lintegral_prod _ ((measurable_radialKernel s r a).norm.ennreal_ofReal.aemeasurable),
    lintegral_norm_radialKernel]
  have HI := (integrable_logRadialKernel hs hr a ha).hasFiniteIntegral
  rw [hasFiniteIntegral_iff_norm] at HI
  exact HI

end PrimeDegreePackets.HeckeMellin


namespace PrimeDegreePackets.HeckeMellin


lemma radialKernel_ofReal {d : ℕ} (s r : ℝ) (a : Fin (d+1) → ℝ)
    {t : ℝ} (ht : 0 < t) (u : LogCoordinates d) :
    radialKernel (s : ℂ) r a t u = (realRadialKernel s r a t u : ℂ) := by
  unfold radialKernel realRadialKernel
  simp only [Complex.ofReal_mul, Complex.ofReal_cpow ht.le, Complex.ofReal_exp]
  push_cast
  congr 2
  all_goals ring

lemma norm_radialKernel {d : ℕ} (s : ℂ) (r : ℝ) (a : Fin (d+1) → ℝ)
    {t : ℝ} (ht : 0 < t) (u : LogCoordinates d) :
    ‖radialKernel s r a t u‖ = realRadialKernel s.re r a t u := by
  unfold radialKernel realRadialKernel
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.norm_exp]
  simp only [Complex.sub_re, Complex.mul_re, Complex.div_ofNat_re,
    Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero, Complex.one_re,
    Complex.neg_re, Complex.ofReal_re]
  push_cast
  congr 2
  all_goals ring

lemma integral_radialKernel_ofReal {d : ℕ} (s r : ℝ) (a : Fin (d+1) → ℝ) :
    (∫ t in Ioi 0, ∫ u, radialKernel (s : ℂ) r a t u) =
      ((∫ t in Ioi 0, ∫ u, realRadialKernel s r a t u : ℝ) : ℂ) := by
  rw [← integral_complex_ofReal]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  simp_rw [radialKernel_ofReal s r a ht, integral_complex_ofReal]

 

theorem integral_realRadialKernel {d : ℕ} {s : ℝ} (hs : 0 < s)
    {r : ℝ} (hr : 0 < r) (a : Fin (d+1) → ℝ) (ha : ∀ i, a i ≠ 0) :
    (∫ t in Ioi 0, ∫ u, realRadialKernel s r a t u) =
      (2/(d+1 : ℝ)) * ((1/2 : ℝ)*r^(-(s/2))*Real.Gamma (s/2))^(d+1) *
        (∏ i, |a i|)^(-s) := by
  have H := integral_radialKernel (s := (s : ℂ)) hs hr a ha
  rw [integral_radialKernel_ofReal] at H
  apply Complex.ofReal_injective
  rw [H]
  have hp : 0 ≤ ∏ i, |a i| := Finset.prod_nonneg (fun _ _ => abs_nonneg _)
  push_cast
  rw [Complex.ofReal_cpow hr.le, Complex.ofReal_cpow hp]
  simp only [Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_ofNat]
  have hg : Complex.Gamma ((s : ℂ)/2) = ((Real.Gamma (s/2) : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_div, Complex.ofReal_ofNat] using Complex.Gamma_ofReal (s/2)
  simp only [hg, Complex.ofReal_prod]

lemma logEnergy_embeddings {d : ℕ} {K : Type*} [Field K]
    (σ : OrderedEmbeddings (d+1) K) (a : K) (u : LogCoordinates d) :
    logEnergy (fun i => σ i a) u = ∑ i, (logFlowWeights u i*σ i a)^2 := by
  simp [logEnergy, restoredLogCoordinates_exp, mul_comm]



lemma measurable_realRadialKernel {d : ℕ} (s r : ℝ) (a : Fin (d+1) → ℝ) :
    Measurable (fun p : ℝ × LogCoordinates d => realRadialKernel s r a p.1 p.2) := by
  unfold realRadialKernel
  have he := continuous_logEnergy a
  fun_prop

lemma ae_positive_first (d : ℕ) :
    ∀ᵐ p : ℝ × LogCoordinates d ∂(volume.restrict (Ioi 0)).prod volume, 0 < p.1 :=
  Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioi)

lemma integrable_realRadialKernel {d : ℕ} {s : ℝ} (hs : 0 < s)
    {r : ℝ} (hr : 0 < r) (a : Fin (d+1) → ℝ) (ha : ∀ i, a i ≠ 0) :
    Integrable (fun p : ℝ × LogCoordinates d => realRadialKernel s r a p.1 p.2)
      ((volume.restrict (Ioi 0)).prod volume) := by
  apply (integrable_radialKernel_product (s := (s : ℂ)) hs hr a ha).norm.congr
  filter_upwards [ae_positive_first d] with p hp
  exact norm_radialKernel (s : ℂ) r a hp p.2

 

theorem lintegral_realRadialKernel {d : ℕ} {s : ℝ} (hs : 0 < s)
    {r : ℝ} (hr : 0 < r) (a : Fin (d+1) → ℝ) (ha : ∀ i, a i ≠ 0) :
    (∫⁻ t in Ioi 0, ∫⁻ u, ENNReal.ofReal (realRadialKernel s r a t u)) =
      ENNReal.ofReal ((2/(d+1 : ℝ)) *
        ((1/2 : ℝ)*r^(-(s/2))*Real.Gamma (s/2))^(d+1) * (∏ i, |a i|)^(-s)) := by
  have HI := integrable_realRadialKernel hs hr a ha
  have Hnn : 0 ≤ᵐ[(volume.restrict (Ioi 0)).prod volume]
      (fun p : ℝ × LogCoordinates d => realRadialKernel s r a p.1 p.2) := by
    filter_upwards [ae_positive_first d] with p hp
    exact mul_nonneg (Real.rpow_nonneg hp.le _) (Real.exp_pos _).le
  rw [← lintegral_prod _ (measurable_realRadialKernel s r a).ennreal_ofReal.aemeasurable,
    ← ofReal_integral_eq_lintegral_ofReal HI Hnn, integral_prod _ HI,
    integral_realRadialKernel hs hr a ha]

 
theorem arithmetic_gaussian_lintegral {d : ℕ} {K : Type*} [Field K] [NumberField K]
    (σ : OrderedEmbeddings (d+1) K) (hn : Module.finrank ℚ K = d+1)
    {a : K} (ha : a ≠ 0) {s : ℝ} (hs : 0 < s) :
    (∫⁻ t in Ioi 0, ENNReal.ofReal (t^((d+1 : ℝ)*s/2-1)) *
      ∫⁻ u : LogCoordinates d, arithmeticFlowGaussian σ a t u) =
      ENNReal.ofReal ((2/(d+1 : ℝ)) *
        ((1/2 : ℝ)*Real.pi^(-(s/2))*Real.Gamma (s/2))^(d+1) *
          |(Algebra.norm ℚ a : ℝ)|^(-s)) := by
  have H := lintegral_realRadialKernel hs Real.pi_pos (fun i => σ i a)
    (fun i => (map_ne_zero (σ i)).mpr ha)
  rw [prod_abs_orderedEmbeddings σ hn] at H
  rw [← H]
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp only
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_congr
  intro u
  rw [realRadialKernel, ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _),
    logEnergy_embeddings]
  rfl

end PrimeDegreePackets.HeckeMellin

open MeasureTheory Set Module
open scoped BigOperators ENNReal NumberField nonZeroDivisors
namespace PrimeDegreePackets.HeckeMellin
open ThetaConstruction

 

lemma idealElementRepresentative_absNorm {K : Type*} [Field K] [NumberField K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (J : integralIdealClassFiber I) :
    |(Algebra.norm ℚ (idealElementRepresentative I J).1.1 : ℝ)| =
      (FractionalIdeal.absNorm I.val : ℝ) * (FractionalIdeal.absNorm J.1.val : ℝ) := by
  have h := congrArg Subtype.val (idealElementRepresentative_spec I J)
  change relativeElementIdeal I (idealElementRepresentative I J).1 = J.val at h
  have hm : J.val*I = toPrincipalIdeal (𝓞 K) K (idealElementRepresentative I J).1 := by
    rw [← h]
    simp [relativeElementIdeal]
  have hn := congrArg (fun U : (FractionalIdeal (𝓞 K)⁰ K)ˣ =>
    (FractionalIdeal.absNorm U.val : ℝ)) hm
  simp only [Units.val_mul, map_mul, coe_toPrincipalIdeal,
    FractionalIdeal.absNorm_span_singleton, Rat.cast_mul, Rat.cast_abs] at hn
  rw [mul_comm] at hn
  exact hn.symm

lemma realHeckeFactor_nonneg (n : ℕ) {s : ℝ} (hs : 0 < s) :
    0 ≤ realHeckeFactor n s := by
  unfold realHeckeFactor
  have hG := Real.Gamma_pos_of_pos (half_pos hs)
  positivity



end PrimeDegreePackets.HeckeMellin


namespace PrimeDegreePackets.HeckeMellin
open ThetaConstruction

 

theorem integralFractionalIdeals_norm_tsum {K : Type*} [Field K] [NumberField K]
    {s : ℝ} (hs : 1 < s) :
    (∑' J : integralFractionalIdeals K,
      ENNReal.ofReal ((FractionalIdeal.absNorm J.1.val : ℝ)^(-s))) =
      ENNReal.ofReal ((NumberField.dedekindZeta K s).re) := by
  rw [tsum_integralFractionalIdeals K (fun J =>
    ENNReal.ofReal ((FractionalIdeal.absNorm J : ℝ)^(-s)))]
  simp only [FractionalIdeal.coeIdeal_absNorm, Rat.cast_natCast]
  rw [integralIdeal_norm_tsum (fun m => ENNReal.ofReal ((m : ℝ)^(-s)))]
  have HE (m : ℕ) :
      (idealCoefficient K m : ℝ≥0∞) * ENNReal.ofReal ((m : ℝ)^(-s)) =
        ENNReal.ofReal (realDirichletTerm (idealCoefficientReal K) s m) := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    congr 1
    simp [realDirichletTerm, idealCoefficientReal, Real.rpow_neg, div_eq_mul_inv]
  simp_rw [HE]
  rw [← ENNReal.ofReal_tsum_of_nonneg
    (realDirichletTerm_nonneg (idealCoefficientReal_nonneg K) s)
    (idealCoefficient_real_summable K hs), ← dedekindZeta_real_eq_terms]


end PrimeDegreePackets.HeckeMellin

open scoped BigOperators ENNReal NumberField nonZeroDivisors Topology
namespace PrimeDegreePackets.HeckeMellin
open ThetaConstruction

lemma idealClass_norm_tsum_ne_top {K : Type*} [Field K] [NumberField K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℝ} (hs : 1 < s) :
    (∑' J : integralIdealClassFiber I,
      ENNReal.ofReal ((FractionalIdeal.absNorm J.1.val : ℝ)^(-s))) ≠ ⊤ := by
  let f : integralIdealClassFiber I → integralFractionalIdeals K := fun J => ⟨J.1,J.2.1⟩
  have hf : Function.Injective f := by
    intro J L H
    exact Subtype.ext (congrArg (fun X : integralFractionalIdeals K => X.val) H)
  have H := ENNReal.tsum_comp_le_tsum_of_injective hf (fun J : integralFractionalIdeals K =>
    ENNReal.ofReal ((FractionalIdeal.absNorm J.1.val : ℝ)^(-s)))
  rw [integralFractionalIdeals_norm_tsum hs] at H
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top H

end PrimeDegreePackets.HeckeMellin
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_DiscriminantBounds
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.finite_nsmulAddKernel_padicInt_pi _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_multiplicative_nthPowerKernel _root_.LocalFieldTheory.finite_nsmulAddKernel_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EmbeddingOrder.toRealOrder_apply _root_.infinitePlace_mult_smul
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
open NumberField Finset
open NumberField Filter Set Topology
open MeasureTheory ProbabilityTheory Matrix
open scoped Classical BigOperators ENNReal
open MeasureTheory Set Filter Topology Module
open scoped BigOperators SchwartzMap
open MeasureTheory Set Filter Topology Module WithLp
open scoped BigOperators SchwartzMap ZeroAtInfty
open scoped FourierTransform
open scoped BigOperators SchwartzMap FourierTransform
open scoped BigOperators FourierTransform
open MeasureTheory Set Filter Topology Module WithLp Asymptotics
open Module WithLp MeasureTheory
open scoped BigOperators Matrix
open Module MeasureTheory
open MeasureTheory Module WithLp
open scoped BigOperators NumberField nonZeroDivisors ENNReal
open Complex Set Metric Filter
open Complex Set Metric Filter MeromorphicOn
open scoped Topology ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology
open MeasureTheory Set Module
open scoped BigOperators ENNReal NumberField nonZeroDivisors
open scoped BigOperators ENNReal NumberField nonZeroDivisors Topology
open Set
open Filter Set Module MeasureTheory
open scoped Topology NumberField
open Filter Set Module MeasureTheory WithLp
open scoped Topology NumberField BigOperators nonZeroDivisors
open scoped Topology NumberField BigOperators nonZeroDivisors ComplexConjugate
open MeasureTheory Set Filter Module WithLp
open scoped Topology BigOperators NumberField nonZeroDivisors
open Complex Set Filter Module
open Complex
open Complex Set Filter
open scoped Topology NumberField ComplexConjugate
open scoped Topology NumberField ComplexConjugate Classical
open Filter Set Topology Module
open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal NNReal ProbabilityTheory
open scoped Matrix Topology Classical ENNReal
open scoped Topology ENNReal
open scoped Matrix Topology ENNReal ProbabilityTheory
open scoped Topology ENNReal CompactlySupported
open MeasureTheory Set Filter TopologicalSpace
open Module Set Matrix MeasureTheory Filter
open scoped NumberField
open CategoryTheory Module
open MeasureTheory Module Set Filter
open scoped BigOperators ENNReal RealInnerProductSpace
open Module Matrix
open scoped NumberField BigOperators

open Module MeasureTheory Set WithLp
open scoped NumberField BigOperators ENNReal


namespace PrimeDegreePackets
open ThetaConstruction

lemma orderedUnitLogOnto_ker_unit_eq_one_or_neg_one {d : ℕ} {K : Type*}
    [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (z : (orderedUnitLogOnto σ).ker) :
    z.val.toMul = 1 ∨ z.val.toMul = -1 := by
  have hz : orderedUnitLog σ z.val = 0 := by
    have h := congrArg Subtype.val z.property
    exact h
  have he := congrFun (logFlowWeights_orderedUnitLog σ z.val.toMul) 0
  rw [show Additive.ofMul z.val.toMul = z.val from rfl, hz] at he
  have ha : |σ 0 (z.val.toMul : K)| = 1 := by
    simpa [logFlowWeights, restoredLogCoordinates, Fin.snoc] using he.symm
  rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp ha with h | h
  · left
    apply Units.ext
    apply NumberField.RingOfIntegers.coe_injective
    apply (σ 0).injective
    simpa using h
  · right
    apply Units.ext
    apply NumberField.RingOfIntegers.coe_injective
    apply (σ 0).injective
    simpa using h

lemma orderedUnitLogOnto_ker_card_totallyReal {d : ℕ} {K : Type*}
    [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) : Nat.card (orderedUnitLogOnto σ).ker = 2 := by
  classical
  have hneg : Additive.ofMul (-1 : (𝓞 K)ˣ) ∈ (orderedUnitLogOnto σ).ker := by
    rw [orderedUnitLogOnto_ker]
    exact neg_one_mem_torsion
  let : Finite (orderedUnitLogOnto σ).ker := by
    rw [orderedUnitLogOnto_ker]
    let e : (NumberField.Units.torsion K).toAddSubgroup ≃ NumberField.Units.torsion K :=
      ⟨(fun u => ⟨u.val.toMul,u.property⟩),(fun u => ⟨Additive.ofMul u.val,u.property⟩),
        (fun _ => rfl),(fun _ => rfl)⟩
    exact Finite.of_injective e e.injective
  let : Fintype (orderedUnitLogOnto σ).ker := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card]
  refine Finset.card_eq_two.mpr ⟨0, ⟨Additive.ofMul (-1),hneg⟩, ?_, ?_⟩
  · intro h
    have he := congrArg (fun z : (orderedUnitLogOnto σ).ker => (z.val.toMul : K)) h
    norm_num at he
  · ext z
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    rcases orderedUnitLogOnto_ker_unit_eq_one_or_neg_one σ z with h | h
    · left
      exact Subtype.ext (congrArg Additive.ofMul h)
    · right
      exact Subtype.ext (congrArg Additive.ofMul h)

end PrimeDegreePackets


end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_IntegerEmbeddings
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.LocalFieldTheory.DiscreteValuationField.finite_nsmulAddKernel_padicInt_pi _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_multiplicative_nthPowerKernel _root_.LocalFieldTheory.finite_nsmulAddKernel_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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
open NumberField Finset
open NumberField Filter Set Topology
open MeasureTheory ProbabilityTheory Matrix
open scoped Classical BigOperators ENNReal
open MeasureTheory Set Filter Topology Module
open scoped BigOperators SchwartzMap
open MeasureTheory Set Filter Topology Module WithLp
open scoped BigOperators SchwartzMap ZeroAtInfty
open scoped FourierTransform
open scoped BigOperators SchwartzMap FourierTransform
open scoped BigOperators FourierTransform
open MeasureTheory Set Filter Topology Module WithLp Asymptotics
open Module WithLp MeasureTheory
open scoped BigOperators Matrix
open Module MeasureTheory
open MeasureTheory Module WithLp
open scoped BigOperators NumberField nonZeroDivisors ENNReal
open Complex Set Metric Filter
open Complex Set Metric Filter MeromorphicOn
open scoped Topology ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology
open MeasureTheory Set Module
open scoped BigOperators ENNReal NumberField nonZeroDivisors
open scoped BigOperators ENNReal NumberField nonZeroDivisors Topology
open Set
open Filter Set Module MeasureTheory
open scoped Topology NumberField
open Filter Set Module MeasureTheory WithLp
open scoped Topology NumberField BigOperators nonZeroDivisors
open scoped Topology NumberField BigOperators nonZeroDivisors ComplexConjugate
open MeasureTheory Set Filter Module WithLp
open scoped Topology BigOperators NumberField nonZeroDivisors
open Complex Set Filter Module
open Complex
open Complex Set Filter
open scoped Topology NumberField ComplexConjugate
open scoped Topology NumberField ComplexConjugate Classical
open Filter Set Topology Module
open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal NNReal ProbabilityTheory
open scoped Matrix Topology Classical ENNReal
open scoped Topology ENNReal
open scoped Matrix Topology ENNReal ProbabilityTheory
open scoped Topology ENNReal CompactlySupported
open MeasureTheory Set Filter TopologicalSpace
open Module Set Matrix MeasureTheory Filter
open scoped NumberField
open CategoryTheory Module
open MeasureTheory Module Set Filter
open scoped BigOperators ENNReal RealInnerProductSpace
open Module Matrix
open scoped NumberField BigOperators
open Module MeasureTheory Set WithLp
open scoped NumberField BigOperators ENNReal
open IntermediateField Module
open Module IntermediateField
open scoped BigOperators NumberField Pointwise
open Module IntermediateField Set
open MeasureTheory Set Module Filter
open scoped BigOperators ENNReal NumberField nonZeroDivisors Topology ComplexConjugate
open Module
open MeasureTheory Module
open scoped BigOperators Matrix NumberField nonZeroDivisors

open scoped BigOperators NumberField nonZeroDivisors


namespace PrimeDegreePackets
open ThetaConstruction
variable {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K]

lemma subgroupUnitLogOnto_surjective (σ : OrderedEmbeddings (d+1) K)
    (S : Subgroup (𝓞 K)ˣ) : Function.Surjective (subgroupUnitLogOnto σ S) := by
  intro p
  obtain ⟨z,hz,H⟩ := (mem_orderedLogSubgroup σ S p.val).mp p.property
  exact ⟨Additive.ofMul ⟨z,hz⟩,Subtype.ext H⟩

instance subgroupUnitLogOnto_ker_finite (σ : OrderedEmbeddings (d+1) K)
    (S : Subgroup (𝓞 K)ˣ) : Finite (subgroupUnitLogOnto σ S).ker := by
  let : Finite (orderedUnitLogOnto σ).ker := Nat.finite_of_card_ne_zero
    (by rw [orderedUnitLogOnto_ker_card_totallyReal σ]; decide)
  exact Finite.of_injective (subgroupUnitLogKernelEmbedding σ S)
    (subgroupUnitLogKernelEmbedding σ S).injective



theorem lintegral_arithmeticFlowGaussian_subgroup
    (σ : OrderedEmbeddings (d+1) K) (S : Subgroup (𝓞 K)ˣ)
    {D : Set (LogCoordinates d)} (hD : IsAddFundamentalDomain (orderedLogSubgroup σ S) D volume)
    (a : K) (t : ℝ) :
    (∫⁻ u in D, ∑' z : S, arithmeticFlowGaussian σ ((z.val:K)*a) t u) =
      (Nat.card (subgroupUnitLogOnto σ S).ker : ℝ≥0∞) *
        ∫⁻ u, arithmeticFlowGaussian σ a t u := by
  let : Countable K := Finsupp.Countable.of_moduleFinite (R := ℚ)
  let : Countable (𝓞 K) := NumberField.RingOfIntegers.coe_injective.countable
  let : Countable (𝓞 K)ˣ := Units.val_injective.countable
  let : Countable (Additive S) := by
    change Countable S
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  let : Countable (orderedLogSubgroup σ S) := (subgroupUnitLogOnto_surjective σ S).countable
  simp_rw [arithmeticFlowGaussian_unit_translate]
  exact lintegral_tsum_addHom_fundamentalDomain (orderedLogSubgroup σ S)
    (subgroupUnitLogOnto σ S) (subgroupUnitLogOnto_surjective σ S) hD
    (arithmeticFlowGaussian σ a t) (arithmeticFlowGaussian_measurable σ a t)

end PrimeDegreePackets


end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_IdealThetaFlow
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupLocallyCompactSpace _root_.finiteLocalUnitsOpen _root_.ideleGroupLocallyCompactSpace _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupLocallyCompactSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EmbeddingOrder.toRealOrder_apply _root_.infinitePlace_mult_smul
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
open NumberField Finset
open NumberField Filter Set Topology
open MeasureTheory ProbabilityTheory Matrix
open scoped Classical BigOperators ENNReal
open MeasureTheory Set Filter Topology Module
open scoped BigOperators SchwartzMap
open MeasureTheory Set Filter Topology Module WithLp
open scoped BigOperators SchwartzMap ZeroAtInfty
open scoped FourierTransform
open scoped BigOperators SchwartzMap FourierTransform
open scoped BigOperators FourierTransform
open MeasureTheory Set Filter Topology Module WithLp Asymptotics
open Module WithLp MeasureTheory
open scoped BigOperators Matrix
open Module MeasureTheory
open MeasureTheory Module WithLp
open scoped BigOperators NumberField nonZeroDivisors ENNReal
open Complex Set Metric Filter
open Complex Set Metric Filter MeromorphicOn
open scoped Topology ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology
open MeasureTheory Set Module
open scoped BigOperators ENNReal NumberField nonZeroDivisors
open scoped BigOperators ENNReal NumberField nonZeroDivisors Topology
open Set
open Filter Set Module MeasureTheory
open scoped Topology NumberField
open Filter Set Module MeasureTheory WithLp
open scoped Topology NumberField BigOperators nonZeroDivisors
open scoped Topology NumberField BigOperators nonZeroDivisors ComplexConjugate
open MeasureTheory Set Filter Module WithLp
open scoped Topology BigOperators NumberField nonZeroDivisors
open Complex Set Filter Module
open Complex
open Complex Set Filter
open scoped Topology NumberField ComplexConjugate
open scoped Topology NumberField ComplexConjugate Classical
open Filter Set Topology Module
open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal NNReal ProbabilityTheory
open scoped Matrix Topology Classical ENNReal
open scoped Topology ENNReal
open scoped Matrix Topology ENNReal ProbabilityTheory
open scoped Topology ENNReal CompactlySupported
open MeasureTheory Set Filter TopologicalSpace
open Module Set Matrix MeasureTheory Filter
open scoped NumberField
open CategoryTheory Module
open MeasureTheory Module Set Filter
open scoped BigOperators ENNReal RealInnerProductSpace
open Module Matrix
open scoped NumberField BigOperators
open Module MeasureTheory Set WithLp
open scoped NumberField BigOperators ENNReal
open IntermediateField Module
open Module IntermediateField
open scoped BigOperators NumberField Pointwise
open Module IntermediateField Set
open MeasureTheory Set Module Filter
open scoped BigOperators ENNReal NumberField nonZeroDivisors Topology ComplexConjugate
open Module
open MeasureTheory Module
open scoped BigOperators Matrix NumberField nonZeroDivisors
open scoped BigOperators NumberField nonZeroDivisors
open MeasureTheory Module WithLp Set
namespace PrimeDegreePackets
open ThetaConstruction

variable {R : Type*} [CommRing R]

variable {d : ℕ} {K : Type*} [Field K] [NumberField K]



theorem subgroupUnitGaussian_mellin_lintegral [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    (S : Subgroup (𝓞 K)ˣ) {D : Set (LogCoordinates d)}
    (hD : IsAddFundamentalDomain (orderedLogSubgroup σ S) D volume)
    {a : K} (ha : a ≠ 0) {s : ℝ} (hs : 0 < s) :
    (∫⁻ t in Ioi 0, ENNReal.ofReal (t^((d+1:ℝ)*s/2-1)) *
      ∫⁻ u in D, ∑' z : S, arithmeticFlowGaussian σ ((z.val:K)*a) t u) =
      (Nat.card (subgroupUnitLogOnto σ S).ker : ℝ≥0∞) *
        ENNReal.ofReal ((2/(d+1:ℝ)) *
          ((1/2:ℝ)*Real.pi^(-(s/2))*Real.Gamma (s/2))^(d+1) *
            |(Algebra.norm ℚ a:ℝ)|^(-s)) := by
  simp_rw [lintegral_arithmeticFlowGaussian_subgroup σ S hD]
  simp_rw [mul_left_comm (ENNReal.ofReal _)
    (Nat.card (subgroupUnitLogOnto σ S).ker : ℝ≥0∞)]
  rw [lintegral_const_mul' _ _ (by simp),
    HeckeMellin.arithmetic_gaussian_lintegral σ hn ha hs]

end PrimeDegreePackets

open scoped BigOperators NumberField ENNReal

open scoped BigOperators NumberField
namespace PrimeDegreePackets
open HeckeMellin
variable {d : ℕ} {K : Type*} [Field K] [NumberField K]

omit [NumberField K] in
lemma complexFlowGaussian_eq_ofReal
    (σ : OrderedEmbeddings (d+1) K) (a : K) (t : ℝ) (u : LogCoordinates d) :
    complexFlowGaussian σ a t u =
      (Real.exp (-Real.pi*t*∑ i, (logFlowWeights u i*σ i a)^2) : ℂ) := by
  rw [Complex.ofReal_exp]
  unfold complexFlowGaussian
  congr 1
  push_cast
  ring

end PrimeDegreePackets


namespace PrimeDegreePackets
open HeckeMellin ThetaConstruction
variable {d : ℕ} {K : Type*} [Field K] [NumberField K]

omit [NumberField K] in
lemma measurable_complexFlowGaussian_joint (σ : OrderedEmbeddings (d+1) K) (a : K) :
    Measurable (fun p : ℝ × LogCoordinates d => complexFlowGaussian σ a p.1 p.2) := by
  unfold complexFlowGaussian
  have HW := continuous_logFlowWeights (d := d)
  fun_prop

omit [NumberField K] in
lemma enorm_complexFlowGaussian (σ : OrderedEmbeddings (d+1) K)
    (a : K) (t : ℝ) (u : LogCoordinates d) :
    ‖complexFlowGaussian σ a t u‖ₑ = arithmeticFlowGaussian σ a t u := by
  rw [← ofReal_norm,complexFlowGaussian_eq_ofReal,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  rfl


lemma measurable_unitOrbitMellinKernel (σ : OrderedEmbeddings (d+1) K)
    (S : Subgroup (𝓞 K)ˣ) (a : K) (s : ℂ) :
    Measurable (unitOrbitMellinKernel σ S a s) := by
  let : Countable K := Finsupp.Countable.of_moduleFinite (R := ℚ)
  let : Countable (𝓞 K) := NumberField.RingOfIntegers.coe_injective.countable
  let : Countable (𝓞 K)ˣ := Units.val_injective.countable
  unfold unitOrbitMellinKernel
  apply Measurable.mul (by fun_prop)
  apply Measurable.tsum
  intro z
  exact measurable_complexFlowGaussian_joint σ _

omit [NumberField K] in
lemma enorm_unitOrbitMellinKernel_le (σ : OrderedEmbeddings (d+1) K)
    (S : Subgroup (𝓞 K)ˣ) (a : K) (s : ℂ) {t : ℝ} (ht : 0 < t)
    (u : LogCoordinates d) :
    ‖unitOrbitMellinKernel σ S a s (t,u)‖ₑ ≤
      ENNReal.ofReal (t^((d+1:ℝ)*s.re/2-1)) *
        ∑' z : S, arithmeticFlowGaussian σ ((z.val:K)*a) t u := by
  unfold unitOrbitMellinKernel
  rw [enorm_mul]
  have HE : ‖(t:ℂ)^(((d+1:ℕ):ℂ)*s/2-1)‖ₑ =
      ENNReal.ofReal (t^((d+1:ℝ)*s.re/2-1)) := by
    rw [← ofReal_norm,Complex.norm_cpow_eq_rpow_re_of_pos ht]
    simp
  rw [HE]
  refine mul_le_mul' le_rfl ?_
  calc
    _ ≤ ∑' z : S, ‖complexFlowGaussian σ ((z.val:K)*a) t u‖ₑ :=
      enorm_tsum_le_tsum_enorm
    _ = _ := by simp_rw [enorm_complexFlowGaussian]

lemma lintegral_enorm_unitOrbitMellinKernel_le [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    (S : Subgroup (𝓞 K)ˣ) {D : Set (LogCoordinates d)}
    (hD : IsAddFundamentalDomain (orderedLogSubgroup σ S) D volume)
    {a : K} (ha : a ≠ 0) {s : ℂ} (hs : 0 < s.re) :
    (∫⁻ p, ‖unitOrbitMellinKernel σ S a s p‖ₑ
      ∂(volume.restrict (Ioi 0)).prod (volume.restrict D)) ≤
      (Nat.card (subgroupUnitLogOnto σ S).ker : ℝ≥0∞) *
        ENNReal.ofReal (realHeckeFactor (d+1) s.re * |(Algebra.norm ℚ a:ℝ)|^(-s.re)) := by
  rw [lintegral_prod _ (measurable_unitOrbitMellinKernel σ S a s).enorm.aemeasurable]
  calc
    _ ≤ ∫⁻ t in Ioi 0, ∫⁻ u in D,
        ENNReal.ofReal (t^((d+1:ℝ)*s.re/2-1)) *
          ∑' z : S, arithmeticFlowGaussian σ ((z.val:K)*a) t u := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact lintegral_mono (fun u => enorm_unitOrbitMellinKernel_le σ S a s ht u)
    _ = _ := by
      simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      rw [subgroupUnitGaussian_mellin_lintegral σ hn S hD ha hs]
      simp only [realHeckeFactor,Nat.cast_add,Nat.cast_one]



end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_UnitOrbitIntegrals
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.ValuationTheory.ValuationSubring.charP _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EmbeddingOrder.toRealOrder_apply _root_.infinitePlace_mult_smul
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
open NumberField Finset
open NumberField Filter Set Topology
open MeasureTheory ProbabilityTheory Matrix
open scoped Classical BigOperators ENNReal
open MeasureTheory Set Filter Topology Module
open scoped BigOperators SchwartzMap
open MeasureTheory Set Filter Topology Module WithLp
open scoped BigOperators SchwartzMap ZeroAtInfty
open scoped FourierTransform
open scoped BigOperators SchwartzMap FourierTransform
open scoped BigOperators FourierTransform
open MeasureTheory Set Filter Topology Module WithLp Asymptotics
open Module WithLp MeasureTheory
open scoped BigOperators Matrix
open Module MeasureTheory
open MeasureTheory Module WithLp
open scoped BigOperators NumberField nonZeroDivisors ENNReal
open Complex Set Metric Filter
open Complex Set Metric Filter MeromorphicOn
open scoped Topology ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology
open MeasureTheory Set Module
open scoped BigOperators ENNReal NumberField nonZeroDivisors
open scoped BigOperators ENNReal NumberField nonZeroDivisors Topology
open Set
open Filter Set Module MeasureTheory
open scoped Topology NumberField
open Filter Set Module MeasureTheory WithLp
open scoped Topology NumberField BigOperators nonZeroDivisors
open scoped Topology NumberField BigOperators nonZeroDivisors ComplexConjugate
open MeasureTheory Set Filter Module WithLp
open scoped Topology BigOperators NumberField nonZeroDivisors
open Complex Set Filter Module
open Complex
open Complex Set Filter
open scoped Topology NumberField ComplexConjugate
open scoped Topology NumberField ComplexConjugate Classical
open Filter Set Topology Module
open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal NNReal ProbabilityTheory
open scoped Matrix Topology Classical ENNReal
open scoped Topology ENNReal
open scoped Matrix Topology ENNReal ProbabilityTheory
open scoped Topology ENNReal CompactlySupported
open MeasureTheory Set Filter TopologicalSpace
open Module Set Matrix MeasureTheory Filter
open scoped NumberField
open CategoryTheory Module
open MeasureTheory Module Set Filter
open scoped BigOperators ENNReal RealInnerProductSpace
open Module Matrix
open scoped NumberField BigOperators
open Module MeasureTheory Set WithLp
open scoped NumberField BigOperators ENNReal
open IntermediateField Module
open Module IntermediateField
open scoped BigOperators NumberField Pointwise
open Module IntermediateField Set
open MeasureTheory Set Module Filter
open scoped BigOperators ENNReal NumberField nonZeroDivisors Topology ComplexConjugate
open Module
open MeasureTheory Module
open scoped BigOperators Matrix NumberField nonZeroDivisors
open scoped BigOperators NumberField nonZeroDivisors
open MeasureTheory Module WithLp Set
open scoped BigOperators NumberField ENNReal
open scoped BigOperators NumberField
open scoped BigOperators NumberField ENNReal nonZeroDivisors
namespace PrimeDegreePackets
open HeckeMellin ThetaConstruction
variable {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K]

lemma tsum_lintegral_unitOrbitMellinKernel_ne_top
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (S : Subgroup (𝓞 K)ˣ)
    {D : Set (LogCoordinates d)}
    (hD : IsAddFundamentalDomain (orderedLogSubgroup σ S) D volume)
    {s : ℂ} (hs : 1 < s.re) :
    (∑' J : integralIdealClassFiber I, ∫⁻ p,
      ‖unitOrbitMellinKernel σ S (idealElementRepresentative I J).1.1 s p‖ₑ
        ∂(volume.restrict (Ioi 0)).prod (volume.restrict D)) ≠ ⊤ := by
  let C : ℝ≥0∞ := (Nat.card (subgroupUnitLogOnto σ S).ker : ℝ≥0∞) *
    ENNReal.ofReal (realHeckeFactor (d+1) s.re * (FractionalIdeal.absNorm I.val:ℝ)^(-s.re))
  have HJ (J : integralIdealClassFiber I) :
      (∫⁻ p, ‖unitOrbitMellinKernel σ S (idealElementRepresentative I J).1.1 s p‖ₑ
        ∂(volume.restrict (Ioi 0)).prod (volume.restrict D)) ≤
      C * ENNReal.ofReal ((FractionalIdeal.absNorm J.1.val:ℝ)^(-s.re)) := by
    have H := lintegral_enorm_unitOrbitMellinKernel_le σ hn S hD
      (idealElementRepresentative I J).1.ne_zero (lt_trans zero_lt_one hs)
    rw [idealElementRepresentative_absNorm,
      Real.mul_rpow (fractionalIdeal_absNorm_pos I).le (fractionalIdeal_absNorm_pos J.1).le,
      ← mul_assoc,ENNReal.ofReal_mul (mul_nonneg
        (realHeckeFactor_nonneg _ (lt_trans zero_lt_one hs))
        (Real.rpow_nonneg (fractionalIdeal_absNorm_pos I).le _)),← mul_assoc] at H
    exact H
  apply ne_top_of_le_ne_top _ (ENNReal.tsum_le_tsum HJ)
  rw [ENNReal.tsum_mul_left]
  apply ENNReal.mul_ne_top _ (idealClass_norm_tsum_ne_top I hs)
  exact ENNReal.mul_ne_top (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) ENNReal.ofReal_ne_top

lemma tsum_lintegral_weightedUnitOrbitMellinKernel_ne_top_oai
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (S : Subgroup (𝓞 K)ˣ)
    {D : Set (LogCoordinates d)}
    (hD : IsAddFundamentalDomain (orderedLogSubgroup σ S) D volume)
    (w : integralIdealClassFiber I → ℂ) (hw : ∀ J, ‖w J‖ ≤ 1)
    {s : ℂ} (hs : 1 < s.re) :
    (∑' J : integralIdealClassFiber I, ∫⁻ p,
      ‖w J * unitOrbitMellinKernel σ S (idealElementRepresentative I J).1.1 s p‖ₑ
        ∂(volume.restrict (Ioi 0)).prod (volume.restrict D)) ≠ ⊤ := by
  apply ne_top_of_le_ne_top (tsum_lintegral_unitOrbitMellinKernel_ne_top σ hn I S hD hs)
  apply ENNReal.tsum_le_tsum
  intro J
  apply lintegral_mono
  intro p
  dsimp only
  rw [enorm_mul]
  apply mul_le_of_le_one_left (by positivity)
  rw [← ofReal_norm]
  exact ENNReal.ofReal_le_one.mpr (hw J)



end PrimeDegreePackets


end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.PrimeDegreePackets.tsum_lintegral_weightedUnitOrbitMellinKernel_ne_top_oai.{u_1} := @OAI.PrimeDegreePackets.tsum_lintegral_weightedUnitOrbitMellinKernel_ne_top_oai.{u_1}
