-- Prove2me | solution 1 for OAI.PrimeDegreePackets.EvenRayCharacter.unramifiedContinued_eq_dirichlet
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T06:56:27.767004+00:00
-- url     : https://prove2.me/submissions/615d3ae2-48a9-4f82-bf7a-be56b9118270

import Mathlib
import Definitions.Def_DukePrimeDegree
import Definitions.Def_OAIQ244Duke044
import Theorems.Thm_OAI_PrimeDegreePackets_HeckeMellin_completedIdealClassXi_eq
import Theorems.Thm_OAI_PrimeDegreePackets_HeckeMellin_idealThetaXi_reflection_totallyReal

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_PrimeFactors
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
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
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.nthRootsSubgroupFintype _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra _root_.scaledRelativeIntegerLatticeQuotientFinite
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
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
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
-- module Solutions.OAIQ244_DUKE.PrimePackets_PrimeSums
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra _root_.scaledRelativeIntegerLatticeQuotientFinite
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
-- module Solutions.OAIQ244_DUKE.PrimePackets_LocalEuler
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra _root_.scaledRelativeIntegerLatticeQuotientFinite
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
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra _root_.scaledRelativeIntegerLatticeQuotientFinite
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



lemma tsum_integralFractionalIdeals (K : Type*) [Field K] [NumberField K]
    (F : FractionalIdeal (𝓞 K)⁰ K → ℝ≥0∞) :
    (∑' J : integralFractionalIdeals K, F J.1) = ∑' J : {J : Ideal (𝓞 K) // J ≠ ⊥}, F J.1 :=
  ((integralFractionalIdealsEquiv K).tsum_eq (fun J => F J.1)).symm



lemma integralEmbeddingMatrix_det_sq {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (σ : OrderedEmbeddings n K) (hn : Module.finrank ℚ K = n)
    (b : Basis (Fin n) ℤ (𝓞 K)) :
    (Matrix.det (fun i j => σ j (b i)))^2 = (NumberField.discr K : ℝ) := by
  let bQ := b.localizationLocalization ℚ ℤ⁰ K
  let B : Matrix (Fin n) (Fin n) ℝ := fun i j => σ j (b i)
  have h := Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two ℚ ℂ bQ (orderedComplexEmbeddings σ hn)
  have hm : Algebra.embeddingsMatrixReindex ℚ ℂ bQ (orderedComplexEmbeddings σ hn) =
      B.map Complex.ofRealHom := by
    ext i j
    change Complex.ofReal (σ j (bQ i)) = Complex.ofReal (σ j (b i))
    rw [show bQ i = (algebraMap (𝓞 K) K) (b i) from b.localizationLocalization_apply ℚ ℤ⁰ K i]
  rw [hm,show (B.map Complex.ofRealHom).det = Complex.ofRealHom B.det from
    (Complex.ofRealHom.map_det B).symm] at h
  have hd : Algebra.discr ℚ bQ = (NumberField.discr K : ℚ) := by
    dsimp only [bQ]
    rw [Algebra.discr_localizationLocalization,NumberField.discr_eq_discr]
    rfl
  rw [hd] at h
  apply Complex.ofReal_injective
  simpa only [B,map_intCast,Complex.ofRealHom_eq_coe,Complex.ofReal_intCast,Complex.ofReal_pow] using h.symm

lemma embeddingMatrix_det_basisChange {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (σ : OrderedEmbeddings n K)
    (b : Basis (Fin n) ℚ K) :
    (embeddingMatrix M σ).det = (b.det (fun i => (M.basis i : K)) : ℝ)*
      Matrix.det (fun i j => σ j (b i)) := by
  let C := b.toMatrix (fun i => (M.basis i : K))
  let B : Matrix (Fin n) (Fin n) ℝ := fun i j => σ j (b i)
  have hm : embeddingMatrix M σ = C.transpose.map (algebraMap ℚ ℝ) * B := by
    ext i j
    have h := congrArg (σ j) (b.sum_repr (M.basis i : K))
    simp only [Algebra.smul_def,map_sum,map_mul,RingHom.map_rat_algebraMap] at h
    exact h.symm
  rw [hm,Matrix.det_mul,show (C.transpose.map (algebraMap ℚ ℝ)).det =
    algebraMap ℚ ℝ C.transpose.det from ((algebraMap ℚ ℝ).map_det C.transpose).symm,
    Matrix.det_transpose]
  rfl

 

theorem embeddingMatrix_abs_det_fractionalIdeal {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (σ : OrderedEmbeddings n K) (hn : Module.finrank ℚ K = n)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    |(embeddingMatrix (fractionalIdealFullLattice hn I) σ).det| =
      Real.sqrt |(NumberField.discr K : ℝ)| * (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ) := by
  let b : Basis (Fin n) ℤ (𝓞 K) := (Module.Free.chooseBasis ℤ (𝓞 K)).reindex
    (Fintype.equivFinOfCardEq (by rw [← Module.finrank_eq_card_basis (Module.Free.chooseBasis ℤ (𝓞 K)),RingOfIntegers.rank,hn]))
  rw [embeddingMatrix_det_basisChange _ σ (b.localizationLocalization ℚ ℤ⁰ K),abs_mul]
  have hnrm := FractionalIdeal.abs_det_basis_change b (I : FractionalIdeal (𝓞 K)⁰ K)
    (fractionalIdealFullLattice hn I).basis
  have hnrm' : |((b.localizationLocalization ℚ ℤ⁰ K).det
      (fun i => ((fractionalIdealFullLattice hn I).basis i : K)) : ℝ)| =
        (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ) := by
    exact_mod_cast hnrm
  rw [hnrm']
  have hdet : |Matrix.det (fun i j => σ j ((b.localizationLocalization ℚ ℤ⁰ K) i))| =
      Real.sqrt |(NumberField.discr K : ℝ)| := by
    simp only [Basis.localizationLocalization_apply]
    conv_rhs => rw [← integralEmbeddingMatrix_det_sq σ hn b,abs_of_nonneg (sq_nonneg _),Real.sqrt_sq_eq_abs]
  rw [hdet,mul_comm]

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
-- module Solutions.OAIQ244_DUKE.PrimePackets_RootOverlaps
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
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

end PrimeDegreePackets


namespace PrimeDegreePackets


lemma half_ne_nonpositive_integer {s : ℂ} (hs : 0 < s.re) (m : ℕ) :
    s/2 ≠ -(m:ℂ) := by
  intro he
  have hr := congrArg Complex.re he
  simp only [Complex.div_ofNat_re,Complex.neg_re,Complex.natCast_re] at hr
  have hm : (0:ℝ) ≤ m := Nat.cast_nonneg m
  linarith

lemma completionExponential_ne_zero (n : ℕ) (D : ℝ) (s : ℂ) :
    completionExponential n D s ≠ 0 := Complex.exp_ne_zero _

end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_LatticeTheta
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EmbeddingOrder.toRealOrder_apply _root_.OAI.DukePrimeDegree.FullLattice.toPacket_carrier _root_.infinitePlace_mult_smul
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


namespace PrimeDegreePackets
open ThetaConstruction
variable {n : ℕ} {K : Type*} [Field K] [NumberField K]

lemma sum_orderedEmbeddings (σ : OrderedEmbeddings n K) (hn : Module.finrank ℚ K = n) (a : K) :
    ∑ i, σ i a = (Algebra.trace ℚ K a : ℝ) := by
  apply Complex.ofReal_injective
  have h := trace_eq_sum_embeddings (K := ℚ) ℂ (x := a)
  rw [← (orderedComplexEmbeddings σ hn).sum_comp] at h
  change (algebraMap ℚ ℂ) (Algebra.trace ℚ K a) = ∑ i, Complex.ofReal (σ i a) at h
  rw [← Complex.ofReal_sum] at h
  change (Algebra.trace ℚ K a : ℂ) = _ at h
  simpa only [Complex.ofReal_ratCast] using h.symm

lemma traceDualFullLattice_basis (M : FullLattice n K) (hn : finrank ℚ K = n) (i : Fin n) :
    ((traceDualFullLattice M hn).basis i : K) =
      (Algebra.traceForm ℚ K).dualBasis (traceForm_nondegenerate ℚ K) (fullLatticeRatBasis M hn) i := by
  exact Basis.coe_span_apply (((Algebra.traceForm ℚ K).dualBasis
    (traceForm_nondegenerate ℚ K) (fullLatticeRatBasis M hn)).linearIndependent.restrict_scalars' ℤ) i

lemma traceDualFullLattice_carrier (M : FullLattice n K) (hn : finrank ℚ K = n) :
    (traceDualFullLattice M hn).carrier = (Algebra.traceForm ℚ K).dualSubmodule M.carrier := by
  rw [← fullLattice_span_basis M]
  simpa only [traceDualFullLattice,← fullLatticeRatBasis_apply M hn] using
    ((Algebra.traceForm ℚ K).dualSubmodule_span_of_basis
      (traceForm_nondegenerate ℚ K) (fullLatticeRatBasis M hn)).symm

lemma traceDual_embeddingMatrix_mul (M : FullLattice n K) (σ : OrderedEmbeddings n K)
    (hn : finrank ℚ K = n) :
    embeddingMatrix (traceDualFullLattice M hn) σ * (embeddingMatrix M σ).transpose = 1 := by
  classical
  ext i j
  simp only [Matrix.mul_apply,embeddingMatrix,Matrix.transpose_apply,← map_mul]
  rw [sum_orderedEmbeddings σ hn]
  have h := (Algebra.traceForm ℚ K).apply_dualBasis_left
    (traceForm_nondegenerate ℚ K) (fullLatticeRatBasis M hn) i j
  rw [traceDualFullLattice_basis]
  simp only [Algebra.traceForm_apply,fullLatticeRatBasis_apply] at h
  rw [h]
  by_cases hij : i = j
  · subst j; simp
  · simp [hij,Ne.symm hij]

end PrimeDegreePackets


open Module MeasureTheory
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_RadialIntegrals
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra _root_.scaledRelativeIntegerLatticeQuotientFinite
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
open scoped ENNReal BigOperators Topology

open MeasureTheory Set Module
open scoped BigOperators ENNReal NumberField nonZeroDivisors


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
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_IdealThetaXi
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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
namespace PrimeDegreePackets.HeckeMellin
open ThetaConstruction

lemma traceDualIdeal_carrier {d : ℕ} {K : Type*} [Field K] [NumberField K]
    (hn : finrank ℚ K = d+1) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    (fractionalIdealFullLattice hn (traceDualIdeal I)).carrier =
      (traceDualFullLattice (fractionalIdealFullLattice hn I) hn).carrier := by
  rw [traceDualFullLattice_carrier]
  change (FractionalIdeal.dual ℤ ℚ I.val : Submodule (𝓞 K) K).restrictScalars ℤ = _
  rw [FractionalIdeal.coe_dual ℤ ℚ I.ne_zero]
  rfl

end PrimeDegreePackets.HeckeMellin
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_ThetaReflection
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra _root_.scaledRelativeIntegerLatticeQuotientFinite
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


namespace PrimeDegreePackets.HeckeMellin
open ThetaConstruction

lemma traceDualIdeal_norm_product {d : ℕ} {K : Type*} [Field K] [NumberField K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    |(NumberField.discr K : ℝ)| * (FractionalIdeal.absNorm (traceDualIdeal I).val : ℝ) *
      (FractionalIdeal.absNorm I.val : ℝ) = 1 := by
  let M := fractionalIdealFullLattice hn I
  let N := fractionalIdealFullLattice hn (traceDualIdeal I)
  have hrow : rowLattice (embeddingMatrix N σ) =
      rowLattice (embeddingMatrix (traceDualFullLattice M hn) σ) := by
    rw [rowLattice_embeddingMatrix, rowLattice_embeddingMatrix, traceDualIdeal_carrier hn I]
  have hdet := abs_det_eq_of_rowLattice_eq _ _
    (embeddingMatrix_det_ne_zero N σ hn)
    (embeddingMatrix_det_ne_zero (traceDualFullLattice M hn) σ hn) hrow
  have H := congrArg (fun A => |Matrix.det A|) (traceDual_embeddingMatrix_mul M σ hn)
  simp only [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one, abs_one, abs_mul] at H
  rw [← hdet, show N = fractionalIdealFullLattice hn (traceDualIdeal I) from rfl,
    show M = fractionalIdealFullLattice hn I from rfl,
    embeddingMatrix_abs_det_fractionalIdeal, embeddingMatrix_abs_det_fractionalIdeal] at H
  calc
    _ = (Real.sqrt |(NumberField.discr K : ℝ)| *
        (FractionalIdeal.absNorm (traceDualIdeal I).val : ℝ)) *
        (Real.sqrt |(NumberField.discr K : ℝ)| * (FractionalIdeal.absNorm I.val : ℝ)) := by
      calc
        _ = (Real.sqrt |(NumberField.discr K : ℝ)|)^2 *
            (FractionalIdeal.absNorm (traceDualIdeal I).val : ℝ) *
            (FractionalIdeal.absNorm I.val : ℝ) := by rw [Real.sq_sqrt (abs_nonneg _)]
        _ = _ := by ring
    _ = 1 := H

end PrimeDegreePackets.HeckeMellin


namespace PrimeDegreePackets.HeckeMellin

lemma traceDual_norm_log {D x y : ℝ} (hD : 0 < D) (hx : 0 < x) (hy : 0 < y)
    (h : D*y*x=1) : Real.log y = -Real.log D-Real.log x := by
  have H := congrArg Real.log h
  rw [Real.log_mul (ne_of_gt (mul_pos hD hy)) (ne_of_gt hx),
    Real.log_mul (ne_of_gt hD) (ne_of_gt hy), Real.log_one] at H
  linarith

lemma norm_sqrt_inv_exp {D x : ℝ} (hD : 0 < D) (hx : 0 < x) :
    (((Real.sqrt D*x)⁻¹ : ℝ) : ℂ) =
      Complex.exp (-((Real.log D : ℂ)/2+(Real.log x : ℂ))) := by
  have he : -((Real.log D : ℂ)/2+(Real.log x : ℂ)) =
      ((-(Real.log D/2+Real.log x) : ℝ) : ℂ) := by push_cast; rfl
  rw [he, ← Complex.ofReal_exp, Complex.ofReal_inj, Real.exp_neg,
    Real.exp_add, ← Real.log_sqrt hD.le, Real.exp_log (Real.sqrt_pos.mpr hD), Real.exp_log hx]

 
lemma traceDual_functional_factor {D x y : ℝ} (hD : 0 < D) (hx : 0 < x) (hy : 0 < y)
    (h : D*y*x=1) (s : ℂ) :
    (x : ℂ)^s * (((Real.sqrt D*x)⁻¹ : ℝ) : ℂ) =
      Complex.exp (((1/2 : ℂ)-s)*(Real.log D : ℂ)) * (y : ℂ)^(1-s) := by
  rw [norm_sqrt_inv_exp hD hx,
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hx)),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hy)),
    ← Complex.ofReal_log hx.le, ← Complex.ofReal_log hy.le,
    ← Complex.exp_add, ← Complex.exp_add, traceDual_norm_log hD hx hy h]
  push_cast
  congr 1
  ring

end PrimeDegreePackets.HeckeMellin


open scoped Topology NumberField BigOperators nonZeroDivisors ComplexConjugate
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_FunctionalEquation
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra _root_.scaledRelativeIntegerLatticeQuotientFinite
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
namespace PrimeDegreePackets.HeckeMellin
open ThetaConstruction

lemma idealThetaXi_normalized_reflection_totallyReal {d : ℕ} {K : Type*}
    [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
     (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) :
    ((FractionalIdeal.absNorm I.val : ℝ) : ℂ)^s * idealThetaXi σ hn I s =
      Complex.exp (((1/2 : ℂ)-s)*(Real.log |(NumberField.discr K : ℝ)| : ℂ)) *
        (((FractionalIdeal.absNorm (traceDualIdeal I).val : ℝ) : ℂ)^(1-s) *
          idealThetaXi σ hn (traceDualIdeal I) (1-s)) := by
  rw [idealThetaXi_reflection_totallyReal σ hn  I s, ← mul_assoc, abs_inv,
    embeddingMatrix_abs_det_fractionalIdeal]
  rw [traceDual_functional_factor (abs_pos.mpr (Int.cast_ne_zero.mpr (NumberField.discr_ne_zero K)))
    (fractionalIdeal_absNorm_pos I) (fractionalIdeal_absNorm_pos (traceDualIdeal I))
    (traceDualIdeal_norm_product σ hn I), mul_assoc]

end PrimeDegreePackets.HeckeMellin


open IntermediateField Module

open Module IntermediateField
open scoped BigOperators NumberField Pointwise
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_NormalClosure
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.ValuationSubring.charP _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceBaseNontriviallyNormedField _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra _root_.scaledRelativeIntegerLatticeQuotientFinite
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


namespace PrimeDegreePackets.HeckeMellin
open ThetaConstruction

lemma integralFractionalIdeals_norm_summable {K : Type*} [Field K] [NumberField K]
    {s : ℝ} (hs : 1 < s) : Summable (fun J : integralFractionalIdeals K =>
      (FractionalIdeal.absNorm J.1.val : ℝ)^(-s)) := by
  have H := ENNReal.summable_toReal (show
    (∑' J : integralFractionalIdeals K,
      ENNReal.ofReal ((FractionalIdeal.absNorm J.1.val : ℝ)^(-s))) ≠ ⊤ from by
    rw [integralFractionalIdeals_norm_tsum hs]; exact ENNReal.ofReal_ne_top)
  simpa only [ENNReal.toReal_ofReal (Real.rpow_nonneg (fractionalIdeal_absNorm_pos _).le _)] using H

end PrimeDegreePackets.HeckeMellin


namespace PrimeDegreePackets.HeckeMellin
open ThetaConstruction


lemma idealThetaXi_zero_value {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    idealThetaXi σ hn I 0 =
      ((volume (orderedThetaLogDomain σ)).toReal : ℂ)*(((d+1 : ℕ) : ℂ)/2) := by
  simp [idealThetaXi, thetaMellinXi, measureReal_def]

lemma idealThetaXi_normalized_one_value {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ((FractionalIdeal.absNorm I.val : ℝ) : ℂ) * idealThetaXi σ hn I 1 =
      Complex.exp ((-1/2 : ℂ)*(Real.log |(NumberField.discr K : ℝ)| : ℂ)) *
        (((volume (orderedThetaLogDomain σ)).toReal : ℂ)*(((d+1 : ℕ) : ℂ)/2)) := by
  have H := idealThetaXi_normalized_reflection_totallyReal σ hn I (1 : ℂ)
  norm_num only [Complex.cpow_one, sub_self, Complex.cpow_zero, one_mul] at H
  rw [H, idealThetaXi_zero_value]
  congr 2
  norm_num

lemma idealClassThetaXi_zero_of_sum_eq_zero {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1) (w : ClassGroup (𝓞 K) → ℂ) (hw : ∑ c, w c = 0) :
    idealClassThetaXi σ hn w 0 = 0 := by
  classical
  simp only [idealClassThetaXi, Complex.cpow_zero, one_mul, idealThetaXi_zero_value]
  have hw' : (∑ c : ClassGroup (𝓞 K), w c⁻¹) = 0 := by
    simpa only [Equiv.inv_apply, hw] using (Equiv.sum_comp (Equiv.inv (ClassGroup (𝓞 K))) w)
  rw [← Finset.sum_mul, hw', zero_mul]

lemma idealClassThetaXi_one_of_sum_eq_zero {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1) (w : ClassGroup (𝓞 K) → ℂ) (hw : ∑ c, w c = 0) :
    idealClassThetaXi σ hn w 1 = 0 := by
  classical
  simp only [idealClassThetaXi, Complex.cpow_one, idealThetaXi_normalized_one_value]
  have hw' : (∑ c : ClassGroup (𝓞 K), w c⁻¹) = 0 := by
    simpa only [Equiv.inv_apply, hw] using (Equiv.sum_comp (Equiv.inv (ClassGroup (𝓞 K))) w)
  rw [← Finset.sum_mul, hw', zero_mul]

end PrimeDegreePackets.HeckeMellin


namespace PrimeDegreePackets.HeckeMellin

lemma finite_group_character_sum_eq_zero {G : Type*} [Group G] [Fintype G]
    (χ : G →* ℂ) (hχ : χ ≠ 1) : ∑ g, χ g = 0 := by
  classical
  obtain ⟨g,hg⟩ : ∃ g, χ g ≠ 1 := by
    by_contra H
    push Not at H
    apply hχ
    ext g
    exact H g
  apply eq_zero_of_mul_eq_self_left hg
  simpa only [Finset.mul_sum, ← map_mul, Equiv.coe_mulLeft] using
    (Equiv.sum_comp (Equiv.mulLeft g) (fun g => χ g))



lemma completedIdealClassXi_zero_of_sum_eq_zero {d : ℕ} {K : Type*}
    [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    (w : ClassGroup (𝓞 K) → ℂ) (hw : ∑ c, w c = 0) :
    completedIdealClassXi σ hn w 0 = 0 := by
  simp only [completedIdealClassXi, idealClassThetaXi_zero_of_sum_eq_zero σ hn w hw, mul_zero]

lemma completedIdealClassXi_one_of_sum_eq_zero {d : ℕ} {K : Type*}
    [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    (w : ClassGroup (𝓞 K) → ℂ) (hw : ∑ c, w c = 0) :
    completedIdealClassXi σ hn w 1 = 0 := by
  simp only [completedIdealClassXi, idealClassThetaXi_one_of_sum_eq_zero σ hn w hw, mul_zero]

 

theorem entireIdealClassL_eq {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1) (w : ClassGroup (𝓞 K) → ℂ) (hw : ∑ c, w c = 0)
    {s : ℂ} (hs : 1 < s.re) :
    entireIdealClassL σ hn w s =
      completionExponential (d+1) |(NumberField.discr K : ℝ)| s *
        Complex.Gamma (s/2)^(d+1)*idealClassDirichlet K w s := by
  have hs0 : s ≠ 0 := Complex.ne_zero_of_one_lt_re hs
  have hs1 : s ≠ 1 := by intro H; simp [H] at hs
  unfold entireIdealClassL
  rw [dslope_of_ne _ hs1, slope, dslope_of_ne _ hs0,
    dslope_of_ne _ (one_ne_zero : (1:ℂ) ≠ 0), slope, slope]
  rw [completedIdealClassXi_zero_of_sum_eq_zero σ hn w hw,
    completedIdealClassXi_one_of_sum_eq_zero σ hn w hw,
    completedIdealClassXi_eq σ hn w hs]
  simp only [vsub_eq_sub, sub_zero, smul_eq_mul]
  field_simp [hs0, sub_ne_zero.mpr hs1]
  ring



end PrimeDegreePackets.HeckeMellin
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_IdealClasses
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.ValuationSubring.charP _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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


namespace PrimeDegreePackets.HeckeMellin



theorem idealClassLFunction_eq {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1) (χ : ClassGroup (𝓞 K) →* ℂ) (hχ : χ ≠ 1)
    {s : ℂ} (hs : 1 < s.re) :
    idealClassLFunction σ hn χ s = idealClassDirichlet K χ s := by
  unfold idealClassLFunction
  rw [entireIdealClassL_eq σ hn χ (finite_group_character_sum_eq_zero χ hχ) hs]
  have hE := completionExponential_ne_zero (d+1) |(NumberField.discr K : ℝ)| s
  have hG := Complex.Gamma_ne_zero (half_ne_nonpositive_integer (by linarith : 0 < s.re))
  rw [inv_pow]
  field_simp


end PrimeDegreePackets.HeckeMellin

open scoped BigOperators ENNReal NumberField nonZeroDivisors Topology ComplexConjugate

open Module
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_RayCharacter
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra _root_.scaledRelativeIntegerLatticeQuotientFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Module Filter Topology
open scoped BigOperators NumberField nonZeroDivisors Classical ComplexConjugate
namespace PrimeDegreePackets
open HeckeMellin ThetaConstruction



variable {K : Type*} [Field K] [NumberField K]



namespace EvenRayCharacter
variable {N : ℕ} (ψ : EvenRayCharacter K N)

lemma idealHom_norm (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ‖(ψ.idealHom J : ℂ)‖ = 1 := by
  obtain ⟨e, he, hpow⟩ := ψ.finiteOrder
  apply (pow_eq_one_iff_of_nonneg (norm_nonneg _) he.ne').mp
  have H := congrArg (fun z : ℂˣ => ‖(z : ℂ)‖) (hpow J)
  simpa only [Units.val_pow_eq_pow_val, norm_pow, Units.val_one, norm_one] using H



lemma underlyingIdeal_unit (J : integralFractionalIdeals K) :
    integralIdealFractionalUnit (underlyingIdeal J) (underlyingIdeal_ne_bot J) = J.val := by
  apply Units.ext
  exact underlyingIdeal_coe J



lemma coefficient_norm_le_one (J : integralFractionalIdeals K) :
    ‖ψ.coefficient J‖ ≤ 1 := by
  classical
  unfold coefficient
  split_ifs
  · exact (ψ.idealHom_norm J.val).le
  · simp only [norm_zero, zero_le_one]



lemma dirichlet_summable {s : ℂ} (hs : 1 < s.re) :
    Summable (fun J : integralFractionalIdeals K =>
      ψ.coefficient J * ((FractionalIdeal.absNorm J.val.val : ℝ) : ℂ)^(-s)) := by
  apply Summable.of_norm_bounded (HeckeMellin.integralFractionalIdeals_norm_summable hs)
  intro J
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (fractionalIdeal_absNorm_pos _),
    Complex.neg_re]
  exact mul_le_of_le_one_left (Real.rpow_nonneg (fractionalIdeal_absNorm_pos _).le _)
    (ψ.coefficient_norm_le_one J)



end EvenRayCharacter
end PrimeDegreePackets

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_RayEuler
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.nthRootsSubgroupFintype _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.intrinsicAbsoluteGaloisT2 _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupT2Space _root_.finiteLocalUnitsOpen _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra _root_.scaledRelativeIntegerLatticeQuotientFinite
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Module Filter Topology
open scoped BigOperators NumberField nonZeroDivisors Classical
namespace PrimeDegreePackets
open HeckeMellin ThetaConstruction
namespace EvenRayCharacter
variable {K : Type*} [Field K] [NumberField K] {N : ℕ}
variable (ψ : EvenRayCharacter K N)


lemma allCoefficient_norm_le_one (I : Ideal (𝓞 K)) :
    ‖ψ.allCoefficient I‖ ≤ 1 := by
  unfold allCoefficient
  split_ifs with hI hc
  · rw [ψ.idealHom_norm]
  · simp
  · simp

lemma allCoefficient_underlying (J : integralFractionalIdeals K) :
    ψ.allCoefficient (underlyingIdeal J) = ψ.coefficient J := by
  rw [allCoefficient, dite_eq_left (underlyingIdeal_ne_bot J)]
  simp only [underlyingIdeal_unit, coefficient]

lemma norm_underlying (J : integralFractionalIdeals K) :
    (Ideal.absNorm (underlyingIdeal J) : ℚ) = FractionalIdeal.absNorm J.val.val := by
  rw [← FractionalIdeal.coeIdeal_absNorm (K := K), underlyingIdeal_coe]


lemma idealTerm_apply {s : ℂ} (hs : 1 < s.re) (I : Ideal (𝓞 K)) :
    ψ.idealTerm hs I = ψ.allCoefficient I * (Ideal.absNorm I : ℂ)^(-s) := rfl

lemma idealTerm_underlying {s : ℂ} (hs : 1 < s.re) (J : integralFractionalIdeals K) :
    ψ.idealTerm hs (underlyingIdeal J) =
      ψ.coefficient J * ((FractionalIdeal.absNorm J.val.val : ℝ) : ℂ)^(-s) := by
  rw [idealTerm_apply, allCoefficient_underlying, ← norm_underlying]
  simp

lemma idealTerm_summable_nonzero {s : ℂ} (hs : 1 < s.re) :
    Summable (fun I : {I : Ideal (𝓞 K) // I ≠ ⊥} => ψ.idealTerm hs I.val) := by
  have H := (ψ.dirichlet_summable hs).comp_injective (integralFractionalIdealsEquiv K).injective
  exact H.congr (fun I => by
    have he : underlyingIdeal ((integralFractionalIdealsEquiv K) I) = I.val :=
      congrArg Subtype.val ((integralFractionalIdealsEquiv K).symm_apply_apply I)
    change ψ.coefficient ((integralFractionalIdealsEquiv K) I) *
      ((FractionalIdeal.absNorm ((integralFractionalIdealsEquiv K) I).val.val : ℝ) : ℂ)^(-s) = _
    have HH := (ψ.idealTerm_underlying hs ((integralFractionalIdealsEquiv K) I)).symm
    erw [he] at HH
    exact HH)

lemma idealTerm_summable {s : ℂ} (hs : 1 < s.re) :
    Summable (ψ.idealTerm hs) := by
  apply (hasSum_subtype_iff_of_support_subset (s := {I : Ideal (𝓞 K) | I ≠ ⊥})
    (f := ψ.idealTerm hs) ?_).mp (ψ.idealTerm_summable_nonzero hs).hasSum |>.summable
  intro I hI hi
  apply hI
  subst I
  exact map_zero _

lemma dirichlet_eq_ideal_tsum {s : ℂ} (hs : 1 < s.re) :
    ψ.dirichlet s = ∑' I : Ideal (𝓞 K), ψ.idealTerm hs I := by
  have HE := (integralFractionalIdealsEquiv K).symm.tsum_eq
    (fun I : {I : Ideal (𝓞 K) // I ≠ ⊥} => ψ.idealTerm hs I.val)
  change (∑' J : integralFractionalIdeals K, _ ) = _ at HE
  have he : ψ.dirichlet s =
      ∑' I : {I : Ideal (𝓞 K) // I ≠ ⊥}, ψ.idealTerm hs I.val := by
    rw [← HE]
    exact tsum_congr (fun J => (ψ.idealTerm_underlying hs J).symm)
  rw [he]
  apply tsum_subtype_eq_of_support_subset
  intro I hI hi
  apply hI
  subst I
  exact map_zero _


lemma normTerm_zero {s : ℂ} (hs : 1 < s.re) : ψ.normTerm hs 0 = 0 := by
  unfold normTerm
  have H : ∀ I : {I : Ideal (𝓞 K) // Ideal.absNorm I = 0}, ψ.idealTerm hs I.val = 0 := by
    intro I
    rw [Ideal.absNorm_eq_zero_iff.mp I.property]
    exact map_zero _
  simp only [H, tsum_zero]

lemma normTerm_one {s : ℂ} (hs : 1 < s.re) : ψ.normTerm hs 1 = 1 := by
  let oneI : {I : Ideal (𝓞 K) // Ideal.absNorm I = 1} := ⟨⊤, Ideal.absNorm_top⟩
  have h : ∀ I : {I : Ideal (𝓞 K) // Ideal.absNorm I = 1}, I = oneI := by
    intro I
    exact Subtype.ext (Ideal.absNorm_eq_one_iff.mp I.property)
  rw [normTerm, tsum_eq_single oneI (fun I hI => (hI (h I)).elim)]
  change ψ.idealTerm hs (⊤ : Ideal (𝓞 K)) = 1
  rw [← Ideal.one_eq_top]
  exact map_one (ψ.idealTerm hs)

lemma normTerm_summable {s : ℂ} (hs : 1 < s.re) : Summable (ψ.normTerm hs) := by
  exact ((ψ.idealTerm_summable hs).hasSum.tsum_fiberwise Ideal.absNorm).summable

lemma normTerm_tsum {s : ℂ} (hs : 1 < s.re) :
    (∑' m : ℕ, ψ.normTerm hs m) = ψ.dirichlet s := by
  rw [ψ.dirichlet_eq_ideal_tsum hs]
  exact ((ψ.idealTerm_summable hs).hasSum.tsum_fiberwise Ideal.absNorm).tsum_eq

lemma normTerm_mul {s : ℂ} (hs : 1 < s.re) {m n : ℕ} (hc : m.Coprime n) :
    ψ.normTerm hs (m*n) = ψ.normTerm hs m * ψ.normTerm hs n := by
  by_cases hm : m = 0
  · simp [hm, ψ.normTerm_zero hs]
  by_cases hn : n = 0
  · simp [hn, ψ.normTerm_zero hs]
  unfold normTerm
  rw [← (idealNormProductEquiv K m n hm hn hc).tsum_eq]
  change (∑' IJ : {I : Ideal (𝓞 K) // Ideal.absNorm I = m} ×
      {J : Ideal (𝓞 K) // Ideal.absNorm J = n}, ψ.idealTerm hs (IJ.1.val * IJ.2.val)) = _
  simp only [map_mul]
  exact (tsum_mul_tsum_of_summable_norm
    ((ψ.idealTerm_summable hs).subtype _).norm
    ((ψ.idealTerm_summable hs).subtype _).norm).symm

lemma prime_idealTerm_norm_lt_one {s : ℂ} (hs : 1 < s.re) {p : ℕ}
    (P : idealsOverPrime K p) : ‖ψ.idealTerm hs P.val‖ < 1 := by
  have H := zetaSummand_norm_lt_one hs (idealsOverPrime_norm_two_le K P.property)
  change ‖ψ.allCoefficient P.val *
    riemannZetaSummandHom (Complex.ne_zero_of_one_lt_re hs) (Ideal.absNorm P.val)‖ < 1
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (ψ.allCoefficient_norm_le_one P.val)).trans_lt H

 

theorem primary_ideal_euler {s : ℂ} (hs : 1 < s.re) {p : ℕ} :
    (∑' I : PrimaryIdeal K p, ψ.idealTerm hs I.val) =
      ∏ P : idealsOverPrime K p, (1 - ψ.idealTerm hs P.val)⁻¹ := by
  have HM (m : Multiset (idealsOverPrime K p)) :
      ψ.idealTerm hs (primaryIdealMultisetEquiv K p m).val =
        (m.map (fun P => ψ.idealTerm hs P.val)).prod := by
    rw [primaryIdealMultisetEquiv_val]
    induction m using Multiset.induction_on with
    | empty => exact map_one _
    | @cons P m ih =>
      simp only [Multiset.map_cons, Multiset.prod_cons, map_mul]
      exact congrArg (fun z => ψ.idealTerm hs P.val * z) ih
  have HT := (complex_tsum_multiset_prod (fun P : idealsOverPrime K p =>
    ψ.idealTerm hs P.val) (ψ.prime_idealTerm_norm_lt_one hs)).2
  rw [← (primaryIdealMultisetEquiv K p).tsum_eq]
  exact (tsum_congr HM).trans HT

theorem local_euler {s : ℂ} (hs : 1 < s.re) {p : ℕ} (hp : p.Prime) :
    (∑' e : ℕ, ψ.normTerm hs (p^e)) =
      ∏ P : idealsOverPrime K p, (1 - ψ.idealTerm hs P.val)⁻¹ := by
  have HS : Summable (fun I : PrimaryIdeal K p => ψ.idealTerm hs I.val) :=
    (ψ.idealTerm_summable hs).subtype _
  have HE := (primaryIdealNormEquiv K p hp).summable_iff.mpr HS
  calc
    _ = ∑' I : Σ e : ℕ, {I : Ideal (𝓞 K) // Ideal.absNorm I = p^e},
        ψ.idealTerm hs I.2.val := HE.tsum_sigma.symm
    _ = ∑' I : PrimaryIdeal K p, ψ.idealTerm hs I.val :=
      (primaryIdealNormEquiv K p hp).tsum_eq (fun I => ψ.idealTerm hs I.val)
    _ = _ := ψ.primary_ideal_euler hs

 
theorem dirichlet_hasProd {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun p : Nat.Primes =>
      ∏ P : idealsOverPrime K (p:ℕ), (1 - ψ.idealTerm hs P.val)⁻¹) (ψ.dirichlet s) := by
  have HE := EulerProduct.eulerProduct_hasProd (ψ.normTerm_one hs)
    (fun h => ψ.normTerm_mul hs h) (ψ.normTerm_summable hs).norm (ψ.normTerm_zero hs)
  rw [ψ.normTerm_tsum hs] at HE
  have he : (fun p : Nat.Primes => ∑' e : ℕ, ψ.normTerm hs ((p:ℕ)^e)) =
      (fun p : Nat.Primes => ∏ P : idealsOverPrime K (p:ℕ),
        (1 - ψ.idealTerm hs P.val)⁻¹) := by
    funext p
    exact ψ.local_euler hs p.property
  rwa [he] at HE



end EvenRayCharacter
end PrimeDegreePackets

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_RayDescent
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.ValuationSubring.charP _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Module Filter Topology
open scoped BigOperators NumberField nonZeroDivisors Classical
namespace PrimeDegreePackets
open HeckeMellin ThetaConstruction
namespace EvenRayCharacter
variable {K : Type*} [Field K] [NumberField K] {N : ℕ}
variable (ψ : EvenRayCharacter K N)

variable [NeZero N]



lemma allCoefficient_of_residue_one (hψ : ψ.residue = 1)
    (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    ψ.allCoefficient I = if IsCoprime I (rationalModulusIdeal (𝓞 K) N) then
      ψ.classCharacter hψ (ClassGroup.mk K (integralIdealFractionalUnit I hI)) else 0 := by
  rw [allCoefficient, dite_eq_left hI]
  split_ifs with hc
  · exact congrArg (fun u : ℂˣ => (u:ℂ)) (ψ.idealHom_eq_classValue hψ I hI hc)
  · rfl


end EvenRayCharacter

variable {K : Type*} [Field K] [NumberField K]



namespace EvenRayCharacter
variable {K : Type*} [Field K] [NumberField K] {N : ℕ}
variable (ψ : EvenRayCharacter K N)

omit [NumberField K] in
lemma coprime_modulus_one (I : Ideal (𝓞 K)) :
    IsCoprime I (rationalModulusIdeal (𝓞 K) 1) := by
  simp only [rationalModulusIdeal, Nat.cast_one, Ideal.span_singleton_one,
    ← Ideal.one_eq_top]
  exact isCoprime_one_right

lemma classRay_coefficient (χ : ClassGroup (𝓞 K) →* ℂˣ)
    (J : integralFractionalIdeals K) :
    (classRayCharacter χ).coefficient J = (χ (ClassGroup.mk K J.val) : ℂ) := by
  simp only [coefficient, coprime_modulus_one, ite_true, if_true, classRayCharacter,
    MonoidHom.comp_apply]

lemma classRay_dirichlet (χ : ClassGroup (𝓞 K) →* ℂˣ) (s : ℂ) :
    (classRayCharacter χ).dirichlet s =
      idealClassDirichlet K (fun c => (χ c : ℂ)) s := by
  apply tsum_congr
  intro J
  rw [classRay_coefficient]

lemma coprime_idealOverPrime_iff {p : ℕ} (hp : p.Prime) (P : idealsOverPrime K p) :
    IsCoprime P.val (rationalModulusIdeal (𝓞 K) N) ↔ ¬ p ∣ N := by
  have hd : P.val ∣ Ideal.span {(p : 𝓞 K)} :=
    UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp P.property)
  constructor
  · intro hc hdiv
    apply (idealsOverPrime_prime K P.property).not_isUnit
    apply hc.isUnit_of_dvd
    apply dvd_trans hd
    rw [Ideal.dvd_iff_le, rationalModulusIdeal, Ideal.span_singleton_le_iff_mem,
      Ideal.mem_span_singleton]
    exact map_dvd (Nat.castRingHom (𝓞 K)) hdiv
  · intro hn
    apply IsCoprime.of_isCoprime_of_dvd_left _ hd
    exact (Ideal.isCoprime_span_singleton_iff _ _).mpr (hp.coprime_iff_not_dvd.mpr hn).cast

end EvenRayCharacter
end PrimeDegreePackets

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_RayUnramified
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.nthRootsSubgroupFintype _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.ValuationSubring.charP _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.intrinsicAbsoluteGaloisT2 _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupT2Space _root_.finiteLocalUnitsOpen _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Module Filter Topology
open scoped BigOperators NumberField nonZeroDivisors Classical
namespace PrimeDegreePackets
open HeckeMellin ThetaConstruction
namespace EvenRayCharacter
variable {K : Type*} [Field K] [NumberField K] {N : ℕ}
variable (ψ : EvenRayCharacter K N)

lemma classRay_allCoefficient (χ : ClassGroup (𝓞 K) →* ℂˣ)
    {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) :
    (classRayCharacter χ).allCoefficient I =
      (χ (ClassGroup.mk K (integralIdealFractionalUnit I hI)) : ℂ) := by
  simp only [allCoefficient, dite_eq_left hI, coprime_modulus_one, ite_true, if_true,
    classRayCharacter, MonoidHom.comp_apply]


lemma mem_badPrimes [NeZero N] (p : Nat.Primes) :
    p ∈ badPrimes N ↔ (p : ℕ) ∣ N := by
  change (⟨p.val, p.property⟩ : {p : ℕ // p.Prime}) ∈
    N.primeFactors.subtype Nat.Prime ↔ _
  simp only [Finset.mem_subtype, Nat.mem_primeFactors,
    p.property, true_and]
  exact and_iff_left (NeZero.ne N)


lemma classEulerCorrection_ne_zero (χ : ClassGroup (𝓞 K) →* ℂˣ)
    (p : Nat.Primes) {s : ℂ} (hs : 0 < s.re) :
    classEulerCorrection χ p s ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro P _
  have hnorm : 1 < (Ideal.absNorm P.val : ℝ) := by
    exact_mod_cast idealsOverPrime_norm_two_le K P.property
  have H : ‖(classRayCharacter χ).allCoefficient P.val *
      (Ideal.absNorm P.val : ℂ)^(-s)‖ < 1 := by
    rw [norm_mul]
    have HN : ‖(Ideal.absNorm P.val : ℂ)^(-s)‖ < 1 := by
      have HN := Complex.norm_cpow_eq_rpow_re_of_pos
        (show 0 < (Ideal.absNorm P.val : ℝ) by linarith) (-s)
      simp only [Complex.ofReal_natCast, Complex.neg_re] at HN
      rw [HN]
      exact Real.rpow_lt_one_of_one_lt_of_neg hnorm (neg_neg_of_pos hs)
    exact (mul_le_of_le_one_left (norm_nonneg _)
      ((classRayCharacter χ).allCoefficient_norm_le_one P.val)).trans_lt HN
  intro hz
  rw [← sub_eq_zero.mp hz, norm_one] at H
  exact (lt_irrefl _ H)

lemma classEulerCorrection_inv (χ : ClassGroup (𝓞 K) →* ℂˣ)
    (p : Nat.Primes) {s : ℂ} (hs : 1 < s.re) :
    ∏ P : idealsOverPrime K (p:ℕ),
      (1 - (classRayCharacter χ).idealTerm hs P.val)⁻¹ =
        (classEulerCorrection χ p s)⁻¹ := by
  rw [classEulerCorrection, ← Finset.prod_inv_distrib]
  rfl

variable [NeZero N]

lemma local_euler_of_residue_one (hψ : ψ.residue = 1)
    (p : Nat.Primes) {s : ℂ} (hs : 1 < s.re) :
    (∏ P : idealsOverPrime K (p:ℕ), (1 - ψ.idealTerm hs P.val)⁻¹) =
      (classEulerCorrection (ψ.classUnitCharacter hψ) p s)⁻¹ *
        (if p ∈ badPrimes N then classEulerCorrection (ψ.classUnitCharacter hψ) p s else 1) := by
  by_cases hb : p ∈ badPrimes N
  · rw [ite_eq_left hb, inv_mul_cancel₀ (classEulerCorrection_ne_zero _ p (by linarith))]
    apply Finset.prod_eq_one
    intro P _
    have hc : ¬ IsCoprime P.val (rationalModulusIdeal (𝓞 K) N) := by
      rw [coprime_idealOverPrime_iff p.property P]
      exact not_not.mpr ((mem_badPrimes p).mp hb)
    have hp0 : P.val ≠ ⊥ := (idealsOverPrime_prime K P.property).ne_zero
    simp only [idealTerm_apply, allCoefficient, dite_eq_left hp0, hc, ite_false, if_false,
      zero_mul, sub_zero, inv_one]
  · rw [ite_eq_right hb, mul_one, ← classEulerCorrection_inv _ p hs]
    apply Finset.prod_congr rfl
    intro P _
    have hc : IsCoprime P.val (rationalModulusIdeal (𝓞 K) N) := by
      rw [coprime_idealOverPrime_iff p.property P]
      exact (mem_badPrimes p).not.mp hb
    have hp0 : P.val ≠ ⊥ := (idealsOverPrime_prime K P.property).ne_zero
    congr 2
    rw [idealTerm_apply, idealTerm_apply, classRay_allCoefficient _ hp0,
      allCoefficient_of_residue_one ψ hψ _ hp0, ite_eq_left hc]
    rfl

 

theorem dirichlet_of_residue_one (hψ : ψ.residue = 1)
    {s : ℂ} (hs : 1 < s.re) :
    ψ.dirichlet s = idealClassDirichlet K (ψ.classCharacter hψ) s *
      badEulerCorrection (ψ.classUnitCharacter hψ) N s := by
  let χ := ψ.classUnitCharacter hψ
  have HF := (classRayCharacter χ).dirichlet_hasProd hs
  simp_rw [classEulerCorrection_inv χ _ hs] at HF
  have HB : HasProd (fun p : Nat.Primes =>
      if p ∈ badPrimes N then classEulerCorrection χ p s else 1)
      (badEulerCorrection χ N s) := by
    have HT := hasProd_prod_of_ne_finset_one (s := badPrimes N)
      (f := fun p : Nat.Primes => if p ∈ badPrimes N then classEulerCorrection χ p s else 1)
      (L := SummationFilter.unconditional _) (fun p hp => ite_eq_right hp)
    simpa only [badEulerCorrection, Finset.prod_ite_mem, Finset.inter_self] using HT
  have H := HF.mul HB
  have HR := ψ.dirichlet_hasProd hs
  simp_rw [ψ.local_euler_of_residue_one hψ _ hs] at HR
  have HE := HR.unique H
  rw [classRay_dirichlet χ s] at HE
  exact HE



theorem unramifiedContinued_eq_dirichlet_oai {d : ℕ} [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    (hψ : ψ.residue = 1) (hχ : ψ.classCharacter hψ ≠ 1)
    {s : ℂ} (hs : 1 < s.re) : ψ.unramifiedContinued σ hn hψ s = ψ.dirichlet s := by
  rw [unramifiedContinued, idealClassLFunction_eq σ hn _ hχ hs]
  exact (ψ.dirichlet_of_residue_one hψ hs).symm

end EvenRayCharacter
end PrimeDegreePackets

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.PrimeDegreePackets.EvenRayCharacter.unramifiedContinued_eq_dirichlet_oai.{u_1} := @OAI.PrimeDegreePackets.EvenRayCharacter.unramifiedContinued_eq_dirichlet_oai.{u_1}
