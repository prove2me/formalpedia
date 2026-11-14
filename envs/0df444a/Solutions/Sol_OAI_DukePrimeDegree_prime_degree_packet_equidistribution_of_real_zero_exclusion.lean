-- Prove2me | solution 1 for OAI.DukePrimeDegree.prime_degree_packet_equidistribution_of_real_zero_exclusion
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T06:54:41.614405+00:00
-- url     : https://prove2.me/submissions/5e6210a8-b791-4d0f-b30e-4a7a30a40019

import Mathlib
import Mathlib.Algebra.Module.Submodule.RestrictScalars
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.RingTheory.Discriminant
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.Localization.Module
import Mathlib.Topology.Sequences
import Definitions.Def_DukePrimeDegree
import Definitions.Def_OAIQ244Duke036
import Theorems.Thm_OAI_DukePrimeDegree_completedXiGap_of_exceptionalRealZeroExclusion
import Theorems.Thm_OAI_DukePrimeDegree_logRegularized_deriv_bound_of_completedXi_gap
import Theorems.Thm_OAI_DukePrimeDegree_packet_limit_isHaar_of_scale_and_EKL
import Theorems.Thm_OAI_PrimeDegreePackets_packet_probability_subsequence_of_zeta_scale
import Theorems.Thm_OAI_PrimeDegreePackets_packet_tight_of_zeta_scale

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

lemma idealCoefficient_one : idealCoefficient K 1 = 1 := by
  simp [idealCoefficient, Ideal.absNorm_eq_one_iff]

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
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
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
-- module Solutions.OAIQ244_DUKE.PrimePackets_IntervalGeometry
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
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
open NumberField Finset Filter Topology
open scoped BigOperators ENNReal nonZeroDivisors

lemma dedekindZeta_real_one_le (K : Type*) [Field K] [NumberField K]
    {s : ℝ} (hs : 1 < s) : 1 ≤ (NumberField.dedekindZeta K s).re := by
  rw [dedekindZeta_real_eq_terms]
  have H := (idealCoefficient_real_summable K hs).le_tsum 1
    (fun m _ => realDirichletTerm_nonneg (idealCoefficientReal_nonneg K) s m)
  simpa [realDirichletTerm,idealCoefficientReal,idealCoefficient_one] using H



end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_ZetaResidues
attribute [-instance] _root_.AlgebraicNumberTheory.numberFieldInRationalSeparableClosure_numberField _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateFieldAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateFieldNumberField _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.KummerTheory.primeCyclotomicBaseNumberField _root_.KummerTheory.rationalCyclotomicLevel_numberField _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupT2Space _root_.finiteLocalUnitsOpen _root_.finiteNormalClosure_numberField _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.FullLattice.toPacket_carrier _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
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
namespace PrimeDegreePackets



lemma tendsto_residue_from_right (K : Type*) [Field K] [NumberField K] :
    Tendsto (fun h : ℝ => h * realDedekindZeta K (1 + h)) (𝓝[>] 0)
      (𝓝 (NumberField.dedekindZeta_residue K)) := by
  have hshift : Tendsto (fun h : ℝ => 1 + h) (𝓝[>] 0) (𝓝[>] 1) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa using (tendsto_const_nhds.add (tendsto_id.mono_left inf_le_left) :
        Tendsto (fun h : ℝ => 1 + h) (𝓝[>] 0) (𝓝 (1 + 0)))
    · filter_upwards [self_mem_nhdsWithin] with h hh
      simpa using hh
  have H := (Complex.continuous_re.tendsto _).comp
    ((NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT K).comp hshift)
  simpa [Function.comp_def, realDedekindZeta, Complex.mul_re] using H

lemma fixed_field_residue_comparison (K : Type*) [Field K] [NumberField K] :
    ∀ᶠ h : ℝ in 𝓝[>] 0,
      NumberField.dedekindZeta_residue K / 2 ≤ h * realDedekindZeta K (1 + h) ∧
      h * realDedekindZeta K (1 + h) ≤ 2 * NumberField.dedekindZeta_residue K := by
  have hk := NumberField.dedekindZeta_residue_pos K
  have ht := tendsto_residue_from_right K
  filter_upwards [ht.eventually_const_lt (by linarith : NumberField.dedekindZeta_residue K / 2 <
      NumberField.dedekindZeta_residue K),
    ht.eventually_lt_const (by linarith : NumberField.dedekindZeta_residue K <
      2 * NumberField.dedekindZeta_residue K)] with h hlo hhi
  exact ⟨hlo.le, hhi.le⟩

 

theorem finite_family_residue_comparison {α : Type*} [Finite α]
    (K : α → Type*) [∀ i, Field (K i)] [∀ i, NumberField (K i)] :
    ∀ᶠ h : ℝ in 𝓝[>] 0, ∀ i,
      NumberField.dedekindZeta_residue (K i) / 2 ≤ h * realDedekindZeta (K i) (1 + h) ∧
      h * realDedekindZeta (K i) (1 + h) ≤ 2 * NumberField.dedekindZeta_residue (K i) := by
  exact Filter.eventually_all.mpr (fun i => fixed_field_residue_comparison (K i))

 
theorem finite_family_residue_reciprocal_bound {α : Type*} [Finite α]
    (K : α → Type*) [∀ i, Field (K i)] [∀ i, NumberField (K i)] :
    ∃ C : ℝ, 0 < C ∧ ∀ i, (NumberField.dedekindZeta_residue (K i))⁻¹ ≤ C := by
  classical
  let := Fintype.ofFinite α
  refine ⟨1 + ∑ i, (NumberField.dedekindZeta_residue (K i))⁻¹, ?_, ?_⟩
  · have : 0 ≤ ∑ i, (NumberField.dedekindZeta_residue (K i))⁻¹ := by
      exact Finset.sum_nonneg (fun i _ => inv_nonneg.mpr (NumberField.dedekindZeta_residue_pos (K i)).le)
    linarith
  · intro i
    have H := Finset.single_le_sum (fun j _ =>
      inv_nonneg.mpr (NumberField.dedekindZeta_residue_pos (K j)).le) (Finset.mem_univ i)
    linarith

 
lemma dedekindZeta_algEquiv {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] (e : K ≃ₐ[ℚ] L) (s : ℂ) :
    NumberField.dedekindZeta K s = NumberField.dedekindZeta L s := by
  let f : 𝓞 K ≃+* 𝓞 L := (e.restrictScalars ℤ).mapIntegralClosure.toRingEquiv
  have hn (I : Ideal (𝓞 K)) : Ideal.absNorm I = Ideal.absNorm (I.map f) := by
    exact Nat.card_congr (Ideal.quotientEquiv I (I.map f) f rfl).toEquiv
  have hc (n : ℕ) : Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} =
      Nat.card {I : Ideal (𝓞 L) // Ideal.absNorm I = n} := by
    apply Nat.card_congr
    exact f.idealComapOrderIso.symm.toEquiv.subtypeEquiv (fun I => by
      change Ideal.absNorm I = n ↔ Ideal.absNorm (I.map f) = n
      rw [hn])
  simp only [NumberField.dedekindZeta, hc]

lemma dedekindZeta_residue_algEquiv {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] (e : K ≃ₐ[ℚ] L) :
    NumberField.dedekindZeta_residue K = NumberField.dedekindZeta_residue L := by
  apply tendsto_nhds_unique (tendsto_residue_from_right K)
  simpa only [realDedekindZeta, dedekindZeta_algEquiv e] using tendsto_residue_from_right L



theorem bounded_discr_residue_data (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ (K : BoundedRealFields N),
        (NumberField.dedekindZeta_residue K.val)⁻¹ ≤ C ∧
        ∀ h : ℝ, 0 < h → h < δ →
          NumberField.dedekindZeta_residue K.val / 2 ≤
            h * realDedekindZeta K.val (1+h) ∧
          h * realDedekindZeta K.val (1+h) ≤
            2 * NumberField.dedekindZeta_residue K.val := by
  obtain ⟨C,hC,HC⟩ := finite_family_residue_reciprocal_bound
    (fun K : BoundedRealFields N => K.val)
  have H := finite_family_residue_comparison (fun K : BoundedRealFields N => K.val)
  obtain ⟨δ,hδ,Hδ⟩ := Metric.mem_nhdsWithin_iff.mp H
  refine ⟨C,hC,δ,hδ,fun K => ⟨HC K,fun h hh hhδ => ?_⟩⟩
  apply Hδ
  exact ⟨by simpa [Real.dist_eq,abs_of_pos hh] using hhδ,hh⟩

 

theorem bounded_discr_residue_comparison (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ (K : Type*) [Field K] [NumberField K],
        (K →+* ℝ) → |NumberField.discr K| ≤ N →
        (NumberField.dedekindZeta_residue K)⁻¹ ≤ C ∧
        ∀ h : ℝ, 0 < h → h < δ →
          NumberField.dedekindZeta_residue K / 2 ≤
            h * realDedekindZeta K (1+h) ∧
          h * realDedekindZeta K (1+h) ≤
            2 * NumberField.dedekindZeta_residue K := by
  obtain ⟨C,hC,δ,hδ,H⟩ := bounded_discr_residue_data N
  refine ⟨C,hC,δ,hδ,?_⟩
  intro K _ _ σ hD
  let f := σ.toRatAlgHom
  let F := f.fieldRange
  let e : K ≃ₐ[ℚ] F := f.equivFieldRange
  let : FiniteDimensional ℚ F := e.toLinearEquiv.finiteDimensional
  let : NumberField F := @NumberField.mk F _ inferInstance inferInstance
  have hd : |NumberField.discr F| ≤ N := by
    rw [← NumberField.discr_eq_discr_of_algEquiv K e]
    exact hD
  let J : BoundedRealFields N := ⟨⟨F,inferInstance⟩,hd⟩
  have HE := H J
  change (NumberField.dedekindZeta_residue F)⁻¹ ≤ C ∧
    ∀ h : ℝ, 0 < h → h < δ →
      NumberField.dedekindZeta_residue F / 2 ≤ h * realDedekindZeta F (1+h) ∧
      h * realDedekindZeta F (1+h) ≤ 2 * NumberField.dedekindZeta_residue F at HE
  simpa only [dedekindZeta_residue_algEquiv e,realDedekindZeta,
    dedekindZeta_algEquiv e] using HE



end PrimeDegreePackets


open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
namespace PrimeDegreePackets

open scoped NumberField nonZeroDivisors



lemma integralElements_scaled_index {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (hn : Module.finrank ℚ K = n) (q : ℕ) :
    ((integralElements K).map (nsmulAddMonoidHom q)).relIndex (integralElements K) = q ^ n := by
  let e : 𝓞 K ≃+ (integralElements K).toIntSubmodule := AddEquiv.refl _
  let : Module.Free ℤ (integralElements K).toIntSubmodule :=
    Module.Free.of_equiv e.toIntLinearEquiv
  let : Module.Finite ℤ (integralElements K).toIntSubmodule :=
    Module.Finite.equiv e.toIntLinearEquiv
  rw [AddSubgroup.relIndex_map_nsmul]
  congr 1
  exact e.toIntLinearEquiv.finrank_eq.symm.trans ((NumberField.RingOfIntegers.rank K).trans hn)

 

theorem multiplierOrder_index_le {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n) :
    (multiplierOrder M).relIndex (integralElements K) ≤ saturationIndex M ^ n := by
  have h := AddSubgroup.relIndex_le_of_le_left
    (scaled_integralElements_le_multiplierOrder M)
    (show ((integralElements K).map (nsmulAddMonoidHom (saturationIndex M))).relIndex
      (integralElements K) ≠ 0 by
        rw [integralElements_scaled_index hn]
        exact pow_ne_zero _ (saturationIndex_ne_zero M))
  rwa [integralElements_scaled_index hn] at h



lemma fieldDiscriminant_one_le (K : Type*) [Field K] [NumberField K] :
    1 ≤ |(NumberField.discr K : ℝ)| := by
  exact_mod_cast Int.one_le_abs (NumberField.discr_ne_zero K)

lemma packetScale_pos {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) : 0 < packetScale M := by
  unfold packetScale
  exact mul_pos (by exact_mod_cast Nat.pos_of_ne_zero (saturationIndex_ne_zero M))
    (Real.sqrt_pos.mpr (lt_of_lt_of_le (by norm_num) (fieldDiscriminant_one_le K)))

 

theorem multiplierDiscriminant_le_packetScale_pow {n : ℕ} {K : Type*}
    [Field K] [NumberField K] (M : FullLattice n K) (hn : Module.finrank ℚ K = n)
    (hnpos : 0 < n) : multiplierDiscriminant M ≤ packetScale M ^ (2 * n) := by
  have hi : ((multiplierOrder M).relIndex (integralElements K) : ℝ) ≤
      (saturationIndex M : ℝ) ^ n := by exact_mod_cast multiplierOrder_index_le M hn
  have hD := fieldDiscriminant_one_le K
  have hDp : |(NumberField.discr K : ℝ)| ≤ |(NumberField.discr K : ℝ)| ^ n :=
    le_self_pow₀ hD hnpos.ne'
  calc
    multiplierDiscriminant M ≤ |(NumberField.discr K : ℝ)| *
        ((saturationIndex M : ℝ) ^ n) ^ 2 := by
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hi 2) (abs_nonneg _)
    _ ≤ |(NumberField.discr K : ℝ)| ^ n * ((saturationIndex M : ℝ) ^ n) ^ 2 :=
      mul_le_mul_of_nonneg_right hDp (sq_nonneg _)
    _ = packetScale M ^ (2 * n) := by
      unfold packetScale
      rw [mul_pow, pow_mul (Real.sqrt _) 2 n, Real.sq_sqrt (abs_nonneg _),
        ← pow_mul, Nat.mul_comm n 2, mul_comm]

 

theorem packetScale_tendsto_of_multiplierDiscriminant_tendsto
    {n : ℕ} (hnpos : 0 < n) (K : ℕ → Type*)
    [∀ i, Field (K i)] [∀ i, NumberField (K i)]
    (M : ∀ i, FullLattice n (K i)) (hn : ∀ i, Module.finrank ℚ (K i) = n)
    (hD : Tendsto (fun i => multiplierDiscriminant (M i)) atTop atTop) :
    Tendsto (fun i => packetScale (M i)) atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [hD.eventually (eventually_gt_atTop (|b| ^ (2 * n)))] with i hi
  have hlt : |b| ^ (2 * n) < packetScale (M i) ^ (2 * n) :=
    hi.trans_le (multiplierDiscriminant_le_packetScale_pow (M i) (hn i) hnpos)
  by_contra hb
  have hle : packetScale (M i) ≤ |b| := (le_of_not_ge hb).trans (le_abs_self b)
  exact (not_lt_of_ge (pow_le_pow_left₀ (packetScale_pos (M i)).le hle _)) hlt



open scoped Pointwise



open FractionalIdeal



end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_ErgodicDecomposition
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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
namespace PrimeDegreePackets

section Transitive
variable {H Y : Type*} [Group H] [MeasurableSpace H] [MeasurableMul₂ H]
  [MeasurableSpace Y]

 

theorem ae_constant_of_transitive_right_action
    (a : Y → H → Y) (ha : Measurable (fun p : Y × H => a p.1 p.2))
    (hmul : ∀ x g h, a (a x g) h = a x (g*h))
    (htrans : ∀ x y, ∃ g, a x g = y)
    (η : Measure H) [SigmaFinite η] [η.IsMulLeftInvariant] [NeZero η]
    (ρ : Measure Y) [SigmaFinite ρ] [NeZero ρ]
    (f : Y → ℝ≥0∞) (hf : Measurable f)
    (hinv : ∀ g, (fun x => f (a x g)) =ᵐ[ρ] f) :
    ∃ c : ℝ≥0∞, f =ᵐ[ρ] (fun _ => c) := by
  have hmeas : MeasurableSet {p : Y × H | f (a p.1 p.2) = f p.1} :=
    measurableSet_eq_fun (hf.comp ha) (hf.comp measurable_fst)
  have hall : ∀ᵐ x ∂ρ, ∀ᵐ g ∂η, f (a x g) = f x :=
    (Measure.ae_ae_comm hmeas).mpr (Eventually.of_forall hinv)
  obtain ⟨x,hx⟩ := hall.exists
  refine ⟨f x,hall.mono ?_⟩
  intro y hy
  obtain ⟨g,hg⟩ := htrans x y
  have hshift : ∀ᵐ h ∂η, f (a x (g*h)) = f x :=
    (measurePreserving_mul_left η g).quasiMeasurePreserving.ae hx
  have hxy : ∀ᵐ h ∂η, f (a y h) = f x := by
    simpa only [← hmul,hg] using hshift
  obtain ⟨h,hh₁,hh₂⟩ := (hy.and hxy).exists
  exact hh₁.symm.trans hh₂

 

theorem invariant_probability_unique_transitive
    (a : Y → H → Y) (ha : Measurable (fun p : Y × H => a p.1 p.2))
    (e : H → Y ≃ᵐ Y) (he : ∀ g x, e g x = a x g)
    (hmul : ∀ x g h, a (a x g) h = a x (g*h))
    (htrans : ∀ x y, ∃ g, a x g = y)
    (η : Measure H) [SigmaFinite η] [η.IsMulLeftInvariant] [NeZero η]
    (μ ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : ∀ g, Measure.map (fun x => a x g) μ = μ)
    (hν : ∀ g, Measure.map (fun x => a x g) ν = ν) : μ = ν := by
  let ρ := μ+ν
  have hρ : ∀ g, Measure.map (fun x => a x g) ρ = ρ := by
    intro g
    change Measure.map (fun x => a x g) (μ+ν) = μ+ν
    have hg : Measurable (fun x => a x g) :=
      ha.comp (measurable_id.prodMk (measurable_const (a := g)))
    rw [Measure.map_add μ ν hg]
    rw [hμ,hν]
  have : NeZero ρ := ⟨by
    intro h
    have := congrArg (fun m : Measure Y => m Set.univ) h
    simp [ρ] at this⟩
  have Hμ : ∃ c : ℝ≥0∞, μ = c • ρ := by
    have hinv (g : H) : (fun x => μ.rnDeriv ρ (a x g)) =ᵐ[ρ] μ.rnDeriv ρ := by
      have H := (e g).measurableEmbedding.rnDeriv_map μ ρ
      have heq : (e g : Y → Y) = (fun x => a x g) := funext (he g)
      rw [heq,hμ,hρ] at H
      exact H
    obtain ⟨c,hc⟩ := ae_constant_of_transitive_right_action a ha hmul htrans η ρ
      (μ.rnDeriv ρ) (Measure.measurable_rnDeriv _ _) hinv
    refine ⟨c,?_⟩
    rw [← Measure.withDensity_rnDeriv_eq μ ρ (Measure.absolutelyContinuous_of_le (show μ ≤ ρ from Measure.le_add_right le_rfl)),
      withDensity_congr_ae hc,withDensity_const]
  have Hν : ∃ c : ℝ≥0∞, ν = c • ρ := by
    have hinv (g : H) : (fun x => ν.rnDeriv ρ (a x g)) =ᵐ[ρ] ν.rnDeriv ρ := by
      have H := (e g).measurableEmbedding.rnDeriv_map ν ρ
      have heq : (e g : Y → Y) = (fun x => a x g) := funext (he g)
      rw [heq,hν,hρ] at H
      exact H
    obtain ⟨c,hc⟩ := ae_constant_of_transitive_right_action a ha hmul htrans η ρ
      (ν.rnDeriv ρ) (Measure.measurable_rnDeriv _ _) hinv
    refine ⟨c,?_⟩
    rw [← Measure.withDensity_rnDeriv_eq ν ρ (Measure.absolutelyContinuous_of_le (show ν ≤ ρ from Measure.le_add_left le_rfl)),
      withDensity_congr_ae hc,withDensity_const]
  obtain ⟨c,hc⟩ := Hμ
  obtain ⟨b,hb⟩ := Hν
  have hceq : c*(2:ℝ≥0∞) = b*2 := by
    have h₁ := congrArg (fun m : Measure Y => m Set.univ) hc
    have h₂ := congrArg (fun m : Measure Y => m Set.univ) hb
    simp only [measure_univ,Measure.smul_apply,smul_eq_mul,ρ,Measure.add_apply] at h₁ h₂
    have H : (1:ℝ≥0∞)+(1:ℝ≥0∞)=2 := by norm_num
    rw [H] at h₁ h₂
    exact h₁.symm.trans h₂
  have hcb : c=b := (ENNReal.mul_left_inj (show (2:ℝ≥0∞) ≠ 0 by norm_num) (show (2:ℝ≥0∞) ≠ ⊤ by norm_num)).mp hceq
  rw [hc,hb,hcb]

end Transitive
end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_HaarUniqueness
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.RootBox.coordinateMeasure_finite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.OAI.PrimeDegreePackets.periodSubmodule_addSubgroup_discrete _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupIsTopologicalGroup _root_.finiteIdeleGroupLocallyCompactSpace _root_.finiteLocalUnitsOpen _root_.ideleGroupIsTopologicalGroup _root_.ideleGroupLocallyCompactSpace _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupLocallyCompactSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one _root_.OAI.DukePrimeDegree.upperRootWordHomeomorph_apply _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.OAI.PrimeDegreePackets.orbitQuotientMap_mk _root_.infinitePlace_mult_smul
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
namespace PrimeDegreePackets
open MeasureTheory Filter Set

lemma rightAction_transitive (n : ℕ) (x y : X n) : ∃ g : G n, rightAction x g = y := by
  obtain ⟨a,rfl⟩ := Quotient.exists_rep x
  obtain ⟨b,rfl⟩ := Quotient.exists_rep y
  refine ⟨a⁻¹*b,?_⟩
  change Quotient.mk _ (a*(a⁻¹*b)) = Quotient.mk _ b
  simp

 

theorem isHaarProbability_unique {n : ℕ} {μ ν : Measure (X n)}
    (hμ : IsHaarProbability μ) (hν : IsHaarProbability ν) : μ = ν := by
  let : MeasurableSpace (G n) := borel (G n)
  let : BorelSpace (G n) := ⟨rfl⟩
  have : IsProbabilityMeasure μ := hμ.1
  have : IsProbabilityMeasure ν := hν.1
  exact invariant_probability_unique_transitive (@rightAction n)
    (continuous_rightAction_uncurry n).measurable
    (fun g => (rightActionHomeomorph g).toMeasurableEquiv) (fun _ _ => rfl)
    (fun x g h => rightAction_mul x g h) (rightAction_transitive n)
    (Measure.haar : Measure (G n)) μ ν hμ.2 hν.2

end PrimeDegreePackets


namespace PrimeDegreePackets
open Filter Set Topology

lemma idealCoefficient_abscissa_le_one (K : Type*) [Field K] [NumberField K] :
    LSeries.abscissaOfAbsConv (fun m => (idealCoefficientReal K m : ℂ)) ≤ 1 := by
  apply LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
  intro y hy
  exact idealCoefficient_LSeriesSummable K (by simpa using hy)

lemma dedekindZeta_differentiableAt (K : Type*) [Field K] [NumberField K]
    {s : ℂ} (hs : 1 < s.re) : DifferentiableAt ℂ (NumberField.dedekindZeta K) s := by
  have hab : LSeries.abscissaOfAbsConv (fun m => (idealCoefficientReal K m : ℂ)) < s.re :=
    (idealCoefficient_abscissa_le_one K).trans_lt (by exact_mod_cast hs)
  have H := (LSeries_hasDerivAt hab).differentiableAt
  have heq : LSeries (fun m => (idealCoefficientReal K m : ℂ)) =
      NumberField.dedekindZeta K := funext (idealCoefficient_LSeries_eq K)
  rw [heq] at H
  exact H



lemma regularizedDedekindZeta_pos (K : Type*) [Field K] [NumberField K]
    {h : ℝ} (hh : 0 < h) : 0 < regularizedDedekindZeta K h := by
  have H := dedekindZeta_real_one_le K (s := 1+h) (by linarith)
  have H' : 1 ≤ (NumberField.dedekindZeta K (1+h)).re := by
    simpa only [Complex.ofReal_add,Complex.ofReal_one] using H
  exact mul_pos hh (lt_of_lt_of_le zero_lt_one H')

lemma regularizedDedekindZeta_differentiableAt (K : Type*) [Field K] [NumberField K]
    {h : ℝ} (hh : 0 < h) : DifferentiableAt ℝ (regularizedDedekindZeta K) h := by
  have H := (dedekindZeta_differentiableAt K (s := (1+h:ℝ)) (by simpa using (show 1 < 1+h by linarith))).hasDerivAt.real_of_complex
  have H' := H.comp h ((hasDerivAt_id h).const_add 1)
  have H'' := (hasDerivAt_id h).mul H'
  change DifferentiableAt ℝ (fun h : ℝ => h*(NumberField.dedekindZeta K (1+(h:ℂ))).re) h
  simpa only [Function.comp_def, Pi.mul_def, id_eq, Complex.ofReal_add,Complex.ofReal_one]
    using H''.differentiableAt

lemma logRegularizedDedekindZeta_differentiableAt (K : Type*) [Field K] [NumberField K]
    {h : ℝ} (hh : 0 < h) : DifferentiableAt ℝ (logRegularizedDedekindZeta K) h :=
  (regularizedDedekindZeta_differentiableAt K hh).log (regularizedDedekindZeta_pos K hh).ne'

lemma tendsto_regularizedDedekindZeta (K : Type*) [Field K] [NumberField K] :
    Tendsto (regularizedDedekindZeta K) (𝓝[>] 0) (𝓝 (NumberField.dedekindZeta_residue K)) := by
  have H := tendsto_residue_from_right K
  change Tendsto (fun h : ℝ => h*(NumberField.dedekindZeta K (1+(h:ℂ))).re) _ _
  simpa only [realDedekindZeta,Complex.ofReal_add,Complex.ofReal_one] using H

lemma tendsto_logRegularizedDedekindZeta (K : Type*) [Field K] [NumberField K] :
    Tendsto (logRegularizedDedekindZeta K) (𝓝[>] 0)
      (𝓝 (Real.log (NumberField.dedekindZeta_residue K))) :=
  (tendsto_regularizedDedekindZeta K).log (NumberField.dedekindZeta_residue_ne_zero K)

 

theorem residue_log_comparison_of_deriv_bound (K : Type*) [Field K] [NumberField K]
    {B C : ℝ} (hB : 0 < B)
    (H : ∀ h ∈ Ioc (0:ℝ) B, |deriv (logRegularizedDedekindZeta K) h| ≤ C)
    {h : ℝ} (hh : 0 < h) (hhB : h ≤ B) :
    |logRegularizedDedekindZeta K h - Real.log (NumberField.dedekindZeta_residue K)| ≤ C*h := by
  have H' : ∀ᶠ u : ℝ in 𝓝[>] 0,
      |logRegularizedDedekindZeta K h-logRegularizedDedekindZeta K u| ≤ C*|h-u| := by
    filter_upwards [self_mem_nhdsWithin,
      (show Tendsto (fun u : ℝ => u) (𝓝[>] 0) (𝓝 0) from tendsto_id.mono_left inf_le_left).eventually_lt_const hB]
      with u hu huB
    have HM := Convex.norm_image_sub_le_of_norm_deriv_le
      (fun u (hu : u ∈ Ioc (0:ℝ) B) => logRegularizedDedekindZeta_differentiableAt K hu.1)
      (fun u hu => by simpa only [Real.norm_eq_abs] using H u hu)
      (convex_Ioc (0:ℝ) B) ⟨hu,huB.le⟩ ⟨hh,hhB⟩
    simpa only [Real.norm_eq_abs] using HM
  have Hleft := ((tendsto_const_nhds (x := logRegularizedDedekindZeta K h)).sub
    (tendsto_logRegularizedDedekindZeta K)).abs
  have Hright : Tendsto (fun u : ℝ => C*|h-u|) (𝓝[>] 0) (𝓝 (C*h)) := by
    have Habs := ((tendsto_const_nhds (x := h)).sub
      (tendsto_id.mono_left inf_le_left : Tendsto (fun u : ℝ => u) (𝓝[>] 0) (𝓝 0))).abs
    simpa only [sub_zero,abs_of_pos hh,id_eq] using Habs.const_mul C
  exact le_of_tendsto_of_tendsto Hleft Hright H'

 
theorem residue_comparison_of_deriv_bound (K : Type*) [Field K] [NumberField K]
    {B C : ℝ} (hB : 0 < B)
    (H : ∀ h ∈ Ioc (0:ℝ) B, |deriv (logRegularizedDedekindZeta K) h| ≤ C)
    {h : ℝ} (hh : 0 < h) (hhB : h ≤ B) :
    Real.exp (-C*h)*NumberField.dedekindZeta_residue K ≤ regularizedDedekindZeta K h ∧
      regularizedDedekindZeta K h ≤ Real.exp (C*h)*NumberField.dedekindZeta_residue K := by
  have HL := residue_log_comparison_of_deriv_bound K hB H hh hhB
  have Htwo := abs_le.mp HL
  have hreg := regularizedDedekindZeta_pos K hh
  have hk := NumberField.dedekindZeta_residue_pos K
  constructor
  · have E := Real.exp_le_exp.mpr (show -C*h+Real.log (NumberField.dedekindZeta_residue K) ≤
        Real.log (regularizedDedekindZeta K h) by
      have hhlo := Htwo.1
      change -(C*h) ≤ Real.log (regularizedDedekindZeta K h)-_ at hhlo
      linarith)
    simpa only [Real.exp_add,Real.exp_log hk,Real.exp_log hreg] using E
  · have E := Real.exp_le_exp.mpr (show Real.log (regularizedDedekindZeta K h) ≤
        C*h+Real.log (NumberField.dedekindZeta_residue K) by
      have hhhi := Htwo.2
      change Real.log (regularizedDedekindZeta K h)-_ ≤ C*h at hhhi
      linarith)
    simpa only [Real.exp_add,Real.exp_log hk,Real.exp_log hreg] using E

end PrimeDegreePackets


end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_ZetaDerivatives
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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
namespace PrimeDegreePackets

 

theorem residue_upper_reciprocal_of_deriv (K : Type*) [Field K] [NumberField K]
    {L C : ℝ} (hL : 0 < L) (hC : 0 < C)
    (H : ∀ h ∈ Ioc (0:ℝ) (4/L), |deriv (logRegularizedDedekindZeta K) h| ≤ C*L) :
    (∀ h ∈ Ioc (0:ℝ) (4/L), regularizedDedekindZeta K h ≤
      Real.exp (4*C)*NumberField.dedekindZeta_residue K) ∧
    (NumberField.dedekindZeta_residue K)⁻¹ ≤ Real.exp (4*C)*L := by
  have hk := NumberField.dedekindZeta_residue_pos K
  have HR (h : ℝ) (hh : h ∈ Ioc (0:ℝ) (4/L)) :
      regularizedDedekindZeta K h ≤ Real.exp (4*C)*NumberField.dedekindZeta_residue K := by
    have HH := (residue_comparison_of_deriv_bound K (by positivity : 0 < 4/L) H hh.1 hh.2).2
    apply HH.trans
    apply mul_le_mul_of_nonneg_right _ hk.le
    apply Real.exp_le_exp.mpr
    have hprod := mul_le_mul_of_nonneg_left ((le_div_iff₀ hL).mp hh.2) hC.le
    nlinarith only [hprod]
  refine ⟨HR,?_⟩
  have hh : 1/L ∈ Ioc (0:ℝ) (4/L) :=
    ⟨one_div_pos.mpr hL,div_le_div_of_nonneg_right (by norm_num) hL.le⟩
  have HS := HR (1/L) hh
  have HZ := dedekindZeta_real_one_le K (s := 1+1/L) (by linarith [hh.1])
  have Hreg : 1/L ≤ regularizedDedekindZeta K (1/L) := by
    unfold regularizedDedekindZeta
    have H := mul_le_mul_of_nonneg_left HZ hh.1.le
    simpa only [Complex.ofReal_add,Complex.ofReal_one,mul_one] using H
  have HP := mul_le_mul_of_nonneg_right (Hreg.trans HS) hL.le
  rw [div_mul_cancel₀ 1 hL.ne'] at HP
  rw [← one_div, div_le_iff₀ hk]
  nlinarith only [HP]

 

theorem uniform_zeta_scale_of_large_discr_deriv
    (n : ℕ) {C D₀ : ℝ} (hC : 0 < C)
    (H : ∀ (K : Type u) [Field K] [NumberField K] [NumberField.IsTotallyReal K],
      Module.finrank ℚ K = n → D₀ ≤ |(NumberField.discr K : ℝ)| →
      ∀ h ∈ Ioc (0:ℝ) (4/Real.log |(NumberField.discr K : ℝ)|),
        |deriv (logRegularizedDedekindZeta K) h| ≤ C*Real.log |(NumberField.discr K : ℝ)|) :
    ∃ A E : ℝ, 0 < A ∧ 0 < E ∧ ∀ᶠ Q : ℝ in atTop,
      ∀ (K : Type u) [Field K] [NumberField K] [NumberField.IsTotallyReal K],
        (K →+* ℝ) → Module.finrank ℚ K = n →
        |(NumberField.discr K : ℝ)| ≤ Q^2 →
        (∀ b : ℝ, Q^(3/4:ℝ) ≤ b →
          realDedekindZeta K (1+1/Real.log b) / Real.log b ≤
            A*NumberField.dedekindZeta_residue K) ∧
        (NumberField.dedekindZeta_residue K)⁻¹ ≤ E*(1+Real.log Q) := by
  obtain ⟨N,hN⟩ := exists_nat_gt (max D₀ (Real.exp 4))
  obtain ⟨B,hB,δ,hδ,Hδ⟩ := bounded_discr_residue_comparison N
  let F : ℝ := Real.exp (4*C)
  refine ⟨max 2 F,2*max B F,lt_of_lt_of_le (by norm_num) (le_max_left _ _),
    mul_pos (by norm_num) (lt_of_lt_of_le hB (le_max_left _ _)),?_⟩
  have hlog : Tendsto (fun Q : ℝ => Real.log (Q^(3/4:ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_rpow_atTop (by norm_num))
  filter_upwards [eventually_ge_atTop (2:ℝ),hlog.eventually_gt_atTop (1/δ),
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<3/4)).eventually_ge_atTop 2]
    with Q hQ hQδ hQpow
  intro K _ _ _ σ hn hdisc
  let L : ℝ := Real.log |(NumberField.discr K : ℝ)|
  have hQp : 0 < Q := by linarith
  have hqlog : 0 < Real.log Q := Real.log_pos (by linarith)
  have hDpos : 0 < |(NumberField.discr K : ℝ)| :=
    abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero K)
  have hLQ : L ≤ 2*Real.log Q := by
    have H := Real.log_le_log hDpos hdisc
    simpa only [L, Real.log_pow, Nat.cast_ofNat] using H
  have hmax : 0 < max B F := lt_of_lt_of_le hB (le_max_left _ _)
  by_cases hsmall : |(NumberField.discr K : ℝ)| ≤ N
  · have hsmall' : |NumberField.discr K| ≤ N := by exact_mod_cast hsmall
    have HB := Hδ K σ hsmall'
    constructor
    · intro b hb
      have hb2 := hQpow.trans hb
      have hlogb : 0 < Real.log b := Real.log_pos (by linarith)
      have hlt : 1/Real.log b < δ := by
        apply (one_div_lt hlogb hδ).mpr
        exact hQδ.trans_le (Real.log_le_log (by linarith) hb)
      have HR := (HB.2 (1/Real.log b) (one_div_pos.mpr hlogb) hlt).2
      calc
        realDedekindZeta K (1+1/Real.log b) / Real.log b ≤
            2*NumberField.dedekindZeta_residue K := by simpa only [one_div,mul_comm,div_eq_mul_inv,one_mul] using HR
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _)
          (NumberField.dedekindZeta_residue_pos K).le
    · apply HB.1.trans
      have hBmax : B ≤ max B F := le_max_left _ _
      nlinarith
  · have hlarge : (N:ℝ) < |(NumberField.discr K : ℝ)| := lt_of_not_ge hsmall
    have hD₀ : D₀ ≤ |(NumberField.discr K : ℝ)| :=
      ((le_max_left _ _).trans_lt hN).le.trans hlarge.le
    have he : Real.exp 4 < |(NumberField.discr K : ℝ)| :=
      (lt_of_le_of_lt (le_max_right _ _) hN).trans hlarge
    have hL4 : 4 < L := by
      have Hlog := Real.log_lt_log (Real.exp_pos 4) he
      simpa only [Real.log_exp] using Hlog
    have hLp : 0 < L := by linarith
    obtain ⟨Hupper,Hrecip⟩ := residue_upper_reciprocal_of_deriv K hLp hC (H K hn hD₀)
    constructor
    · intro b hb
      have hb2 := hQpow.trans hb
      have hlogb : 0 < Real.log b := Real.log_pos (by linarith)
      have hloglow : (3/4:ℝ)*Real.log Q ≤ Real.log b := by
        have HE := Real.log_le_log (Real.rpow_pos_of_pos hQp _) hb
        simpa only [Real.log_rpow hQp] using HE
      have hbound : 1/Real.log b ≤ 4/L := by
        rw [div_le_div_iff₀ hlogb hLp]
        nlinarith only [hLQ,hloglow,hqlog]
      have HU := Hupper (1/Real.log b) ⟨one_div_pos.mpr hlogb,hbound⟩
      calc
        realDedekindZeta K (1+1/Real.log b) / Real.log b ≤ F*NumberField.dedekindZeta_residue K := by
          simpa only [F,regularizedDedekindZeta,realDedekindZeta,Complex.ofReal_add,
            Complex.ofReal_one,one_div,mul_comm,div_eq_mul_inv,one_mul] using HU
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _)
          (NumberField.dedekindZeta_residue_pos K).le
    · apply Hrecip.trans
      have hF : 0 < F := Real.exp_pos _
      have hFmax : F ≤ max B F := le_max_right _ _
      calc
        F*L ≤ F*(2*Real.log Q) := mul_le_mul_of_nonneg_left hLQ hF.le
        _ ≤ (max B F)*(2*Real.log Q) := mul_le_mul_of_nonneg_right hFmax (by positivity)
        _ ≤ _ := by nlinarith

end PrimeDegreePackets


namespace PrimeDegreePackets

lemma complex_digamma_continuousAt_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    ContinuousAt Complex.digamma s := by
  let D : Set ℂ := {z | 0 < z.re}
  have ho : IsOpen D := Complex.continuous_re.isOpen_preimage _ isOpen_Ioi
  have hall : ∀ z ∈ D, ∀ m : ℕ, z ≠ -(m:ℂ) := by
    intro z hz m hm
    have hh : 0 < z.re := hz
    rw [hm] at hh
    simp only [Complex.neg_re,Complex.natCast_re] at hh
    exact (not_lt_of_ge (neg_nonpos.mpr (Nat.cast_nonneg m))) hh
  have hd : DifferentiableOn ℂ Complex.Gamma D := by
    intro z hz
    exact (Complex.differentiableAt_Gamma z (hall z hz)).differentiableWithinAt
  have ha := hd.analyticOnNhd ho s hs
  exact ha.deriv.continuousAt.div ha.continuousAt (Complex.Gamma_ne_zero (hall s hs))

lemma archimedeanZetaTerm_continuousOn (n : ℕ) :
    ContinuousOn (archimedeanZetaTerm n) (Icc 1 2) := by
  intro s hs
  apply ContinuousAt.continuousWithinAt
  unfold archimedeanZetaTerm
  apply ContinuousAt.const_mul
  apply ContinuousAt.sub _ continuousAt_const
  apply Complex.continuous_re.continuousAt.comp
  have hc0 : ContinuousAt (fun t : ℝ => (t:ℂ)/2) s :=
    Complex.continuous_ofReal.continuousAt.div_const 2
  have hp : 0 < ((s:ℂ)/2).re := by
    have hs1 := hs.1
    simp only [Complex.div_ofNat_re,Complex.ofReal_re]
    positivity
  exact ContinuousAt.comp (f := fun t : ℝ => (t:ℂ)/2)
    (complex_digamma_continuousAt_of_re_pos hp) hc0

lemma archimedeanZetaTerm_bounded (n : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ s ∈ Icc (1:ℝ) 2, |archimedeanZetaTerm n s| ≤ B := by
  obtain ⟨B,hB⟩ := (isCompact_Icc.bddAbove_image
    (archimedeanZetaTerm_continuousOn n).abs)
  refine ⟨max B 1,lt_of_lt_of_le zero_lt_one (le_max_right _ _),?_⟩
  intro s hs
  exact (hB (Set.mem_image_of_mem _ hs)).trans (le_max_left _ _)



end PrimeDegreePackets


open MeasureTheory Filter Set Matrix
open scoped Topology Classical
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Arithmetic_StarkZeros
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Uniform residues from completed-zeta zero separation

The completed zeta function, its functional equation and its convergent
real Hadamard sum give the uniform residue estimate from a uniform zero
gap. Uniqueness of a near-one zero reduces this gap to real-zero exclusion.
-/

open Filter Set MeasureTheory
open scoped Topology

namespace DukePrimeDegree

open PrimeDegreePackets PrimeDegreePackets.AnalyticGrowth
  PrimeDegreePackets.HeckeMellin

universe u

/-- The completed-zeta zero gap gives the uniform zeta scale bound. -/
theorem uniformZetaScaleBound_of_completedXiGap (d : ℕ)
    (H : CompletedXiGap.{u} d) : UniformZetaScaleBound.{u} (d + 1) := by
  classical
  obtain ⟨c, L₀, hc, hL₀, Hgap⟩ := H
  obtain ⟨B, hB, harch⟩ := archimedeanZetaTerm_bounded (d + 1)
  let C := 4 * (1 + 3 / c) ^ 2 * (3 + B) + B + 2
  have hC : 0 < C := by dsimp [C] <;> positivity
  obtain ⟨A, E, hA, _, Hscale⟩ :=
    uniform_zeta_scale_of_large_discr_deriv (d + 1) (D₀ := Real.exp L₀) hC (by
      intro K _ _ _ hn hD
      let : Algebra.IsAlgebraic ℚ K := NumberField.isAlgebraic K
      let : Algebra.IsSeparable ℚ K :=
        Algebra.IsAlgebraic.isSeparable_of_perfectField
      let σc : EmbeddingOrder K (d + 1) :=
        (Fintype.equivFinOfCardEq (by rw [AlgHom.card, hn])).symm
      let σ : OrderedEmbeddings (d + 1) K := σc.toRealOrder
      have hL : L₀ ≤ Real.log |(NumberField.discr K : ℝ)| := by
        apply (Real.le_log_iff_exp_le (abs_pos.mpr
          (show (NumberField.discr K : ℝ) ≠ 0 from by exact_mod_cast NumberField.discr_ne_zero K))).mpr
        exact hD
      exact logRegularized_deriv_bound_of_completedXi_gap σ hn hc hB rfl
        (hL₀.trans hL) harch (Hgap K hn σ hL))
  refine ⟨A, hA, ?_⟩
  filter_upwards [Hscale] with Q hQ
  intro K _ _ _ σ hn hD
  exact (hQ K σ hn hD).1

end DukePrimeDegree

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_Convergence
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Compactness and uniqueness of probability limits

Tightness and uniqueness of subsequential limits imply weak convergence,
as in the final compactness argument for prime-degree torus packets.
-/

open MeasureTheory Filter Set
open scoped Topology

namespace DukePrimeDegree

/-- Tight probability measures converge if every convergent subsequence
has the specified limit. Prokhorov compactness ensures that this statement
also rules out loss of mass. -/
theorem tendsto_of_tight_of_unique_subsequential_limit
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] [T2Space X] [FirstCountableTopology (ProbabilityMeasure X)]
    (μ : ℕ → ProbabilityMeasure X) (m : ProbabilityMeasure X)
    (htight : IsTightMeasureSet {ν : Measure X | ∃ i, ν = μ i})
    (hlimit : ∀ (φ : ℕ → ℕ), StrictMono φ → ∀ ν : ProbabilityMeasure X,
      Tendsto (μ ∘ φ) atTop (𝓝 ν) → ν = m) :
    Tendsto μ atTop (𝓝 m) := by
  have hcompact : IsCompact (closure (range μ)) := by
    apply isCompact_closure_of_isTightMeasureSet
    convert htight using 1
    all_goals try with_reducible_and_instances rfl
    ext ν
    simp only [mem_ofPred_eq, mem_range]
    constructor
    · rintro ⟨ρ, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨μ i, ⟨i, rfl⟩, rfl⟩
  apply hcompact.tendsto_nhds_of_unique_mapClusterPt
    (Eventually.of_forall (fun i => subset_closure (mem_range_self i)))
  intro ν _ hν
  obtain ⟨φ, hφ, hconv⟩ := hν.tendsto_subseq
  exact hlimit φ hφ ν hconv

end DukePrimeDegree

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_MainConditional
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.RootBox.coordinateMeasure_finite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.OAI.PrimeDegreePackets.periodSubmodule_addSubgroup_discrete _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupT2Space _root_.finiteLocalUnitsOpen _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Conditional prime-degree packet equidistribution

Complete volume-weighted local-homothety packets converge to Haar
probability and form a tight family under a residue-relative uniform
zeta scale bound and prime-degree positive-entropy rigidity. The
arithmetic and dynamical hypotheses concern the actual homogeneous
lattice space and its diagonal action. A subsequential packet limit
supplies Haar probability.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology

namespace DukePrimeDegree

open PrimeDegreePackets

universe u

/-- The full volume-weighted packet conclusion, including no escape of
mass, conditional on the explicitly separated analytic and published
rigidity inputs. The family may vary through arbitrary full lattices and
arbitrary local homothety types. -/
theorem prime_degree_packet_equidistribution_of_scale_and_EKL
    (d : ℕ) (hprime : Nat.Prime (d + 1)) (hfive : 5 ≤ d + 1)
    (Hscale : UniformZetaScaleBound.{u} (d + 1)) (ekl : EKLPrimeInput d)
    (K : ℕ → Type u) [∀ i, Field (K i)] [∀ i, NumberField (K i)]
    [∀ i, NumberField.IsTotallyReal (K i)]
    (M : ∀ i, PrimeDegreePackets.FullLattice (d + 1) (K i))
    (σ : ∀ i, OrderedEmbeddings (d + 1) (K i))
    (hn : ∀ i, Module.finrank ℚ (K i) = d + 1)
    (hD : Tendsto (fun i => PrimeDegreePackets.multiplierDiscriminant (M i)) atTop atTop) :
    ∃ ν : ProbabilityMeasure (X (d + 1)),
      IsHaarProbability (ν : Measure (X (d + 1))) ∧
      Tendsto (fun i => packetProbability (M i) (σ i) (hn i)
        (hprime.odd_of_ne_two (by omega))) atTop (𝓝 ν) ∧
      IsTightMeasureSet (Set.range (fun i => packetMeasure (M i) (σ i))) := by
  let hodd : Odd (d + 1) := hprime.odd_of_ne_two (by omega)
  let p : ℕ → ProbabilityMeasure (X (d + 1)) :=
    fun i => packetProbability (M i) (σ i) (hn i) hodd
  have hQ := packetScale_tendsto_of_multiplierDiscriminant_tendsto
    (Nat.succ_pos d) K M hn hD
  have htight := packet_tight_of_zeta_scale d hodd Hscale K M σ hn hQ
  obtain ⟨ν, φ, hφ, hsub⟩ :=
    packet_probability_subsequence_of_zeta_scale d hodd Hscale K M σ hn hD
  have hHaar := packet_limit_isHaar_of_scale_and_EKL d hprime (by omega) hodd Hscale ekl
    (fun i => K (φ i)) (fun i => M (φ i)) (fun i => σ (φ i))
    (fun i => hn (φ i)) (hD.comp hφ.tendsto_atTop) ν hsub
  refine ⟨ν, hHaar, ?_, htight⟩
  have htight' : IsTightMeasureSet {μ : Measure (X (d + 1)) | ∃ i, μ = p i} := by
    convert htight using 1
    all_goals try with_reducible_and_instances rfl
    ext μ
    simp only [Set.mem_ofPred_eq, Set.mem_range]
    constructor <;> rintro ⟨i, hi⟩ <;> exact ⟨i, hi.symm⟩
  apply tendsto_of_tight_of_unique_subsequential_limit p ν htight'
  intro ψ hψ ξ hξ
  have hHaarξ := packet_limit_isHaar_of_scale_and_EKL d hprime (by omega) hodd Hscale ekl
    (fun i => K (ψ i)) (fun i => M (ψ i)) (fun i => σ (ψ i))
    (fun i => hn (ψ i)) (hD.comp hψ.tendsto_atTop) ξ hξ
  exact Subtype.ext (isHaarProbability_unique hHaarξ hHaar)

end DukePrimeDegree

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_MainReduction
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Packet equidistribution from exceptional-zero exclusion

Completed-zeta continuation, the zero sum and complex zero separation
reduce the analytic hypothesis to real exceptional-zero exclusion.
Together with prime-degree positive-entropy rigidity, this gives
convergence of complete packets and tightness.
-/

open MeasureTheory Filter
open scoped Topology

namespace DukePrimeDegree

open PrimeDegreePackets

universe u

/-- Theorem 1.1 with all of Stark's analytic ingredients discharged.
Only real exceptional-zero exclusion and measure rigidity remain. -/
theorem prime_degree_packet_equidistribution_of_real_zero_exclusion_oai
    (d : ℕ) (hprime : Nat.Prime (d + 1)) (hfive : 5 ≤ d + 1)
    (stark : ExceptionalRealZeroExclusion.{u} d) (ekl : EKLPrimeInput d)
    (K : ℕ → Type u) [∀ i, Field (K i)] [∀ i, NumberField (K i)]
    [∀ i, NumberField.IsTotallyReal (K i)]
    (M : ∀ i, PrimeDegreePackets.FullLattice (d + 1) (K i))
    (σ : ∀ i, OrderedEmbeddings (d + 1) (K i))
    (hn : ∀ i, Module.finrank ℚ (K i) = d + 1)
    (hD : Tendsto (fun i => PrimeDegreePackets.multiplierDiscriminant (M i)) atTop atTop) :
    ∃ ν : ProbabilityMeasure (X (d + 1)),
      IsHaarProbability (ν : Measure (X (d + 1))) ∧
      Tendsto (fun i => packetProbability (M i) (σ i) (hn i)
        (hprime.odd_of_ne_two (by omega))) atTop (𝓝 ν) ∧
      IsTightMeasureSet (Set.range (fun i => packetMeasure (M i) (σ i))) := by
  exact prime_degree_packet_equidistribution_of_scale_and_EKL d hprime hfive
    (uniformZetaScaleBound_of_completedXiGap d
      (completedXiGap_of_exceptionalRealZeroExclusion d stark)) ekl K M σ hn hD

end DukePrimeDegree

end OAI
end

theorem solution.{u} : type_of% @OAI.DukePrimeDegree.prime_degree_packet_equidistribution_of_real_zero_exclusion_oai.{u} := @OAI.DukePrimeDegree.prime_degree_packet_equidistribution_of_real_zero_exclusion_oai.{u}
