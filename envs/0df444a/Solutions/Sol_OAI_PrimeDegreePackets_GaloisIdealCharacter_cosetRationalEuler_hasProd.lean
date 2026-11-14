-- Prove2me | solution 1 for OAI.PrimeDegreePackets.GaloisIdealCharacter.cosetRationalEuler_hasProd
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T06:42:24.512604+00:00
-- url     : https://prove2.me/submissions/c558e8e9-ae0c-476a-a6b4-b78c31e9a5b2

import Mathlib
import Definitions.Def_OAIQ244Duke023
import Definitions.Def_OAIQ244Duke024

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_FrobeniusOrder
attribute [-instance] _root_.HilbertRamification.Dedekind.basePrime_isPrime _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedMaximalIdeal.instLiesOver _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Module
open scoped NumberField Classical
namespace PrimeDegreePackets.GaloisIdealCharacter
attribute [local instance] Ideal.Quotient.field
variable (F E : Type*) [Field F] [NumberField F] [Field E] [NumberField E]
variable [Algebra F E] [FiniteDimensional F E] [IsGalois F E]

omit [FiniteDimensional F E] in
lemma isArithFrobAt_restrict_pow_mk
    (Q : Ideal (𝓞 E)) (σ : E ≃ₐ[F] E) (H : IsArithFrobAt (𝓞 F) σ Q)
    (n : ℕ) (x : 𝓞 E) :
    Ideal.Quotient.mk Q ((σ ^ n) • x) =
      (H.restrict ^ n) (Ideal.Quotient.mk Q x) := by
  induction n with
  | zero => simp only [pow_zero, one_smul, AlgHom.one_apply]
  | succ n ih =>
    rw [pow_succ', mul_smul]
    change Ideal.Quotient.mk Q ((MulSemiringAction.toAlgHom (𝓞 F) (𝓞 E) σ)
      ((σ ^ n) • x)) = _
    rw [← H.restrict_mk, ih, pow_succ', AlgHom.mul_apply]

 

omit [FiniteDimensional F E] in
theorem orderOf_eq_inertiaDeg_of_isArithFrobAt
    (P : Ideal (𝓞 F)) (Q : Ideal (𝓞 E))
    [P.IsMaximal] [Q.IsMaximal] [Q.LiesOver P]
    [Algebra.IsUnramifiedAt (𝓞 F) Q]
    (σ : E ≃ₐ[F] E) (H : IsArithFrobAt (𝓞 F) σ Q) :
    orderOf σ = Q.inertiaDeg (𝓞 F) := by
  let : FaithfulSMul (E ≃ₐ[F] E) (𝓞 E) := IsGaloisGroup.faithful (𝓞 F)
  have horder : orderOf σ = orderOf H.restrict := by
    apply orderOf_eq_orderOf_iff.mpr
    intro n
    constructor
    · intro hn
      apply AlgHom.ext
      intro x
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [← isArithFrobAt_restrict_pow_mk F E Q σ H n x, hn, one_smul]
      rfl
    · intro hn
      have Hn : IsArithFrobAt (𝓞 F) (σ ^ (n + 1)) Q := by
        intro x
        apply Ideal.Quotient.eq_zero_iff_mem.mp
        rw [map_sub, map_pow]
        change Ideal.Quotient.mk Q ((σ ^ (n + 1)) • x) -
          Ideal.Quotient.mk Q x ^ Nat.card ((𝓞 F) ⧸ Q.under (𝓞 F)) = 0
        rw [isArithFrobAt_restrict_pow_mk F E Q σ H, pow_succ, hn, one_mul,
          H.restrict_apply, sub_self]
      have he : σ ^ (n + 1) = σ := by
        apply MulSemiringAction.toAlgHom_injective (𝓞 F) (𝓞 E)
        exact Hn.eq_of_isUnramifiedAt H Q.primeCompl_le_nonZeroDivisors
      exact mul_right_cancel (by simpa only [pow_succ, one_mul] using he :
        σ ^ n * σ = 1 * σ)
  let : (Q.under (𝓞 F)).IsMaximal := by
    rw [← Q.over_def P]
    infer_instance
  let : Fintype ((𝓞 F) ⧸ Q.under (𝓞 F)) := Fintype.ofFinite _
  have hr : H.restrict = FiniteField.frobeniusAlgHom
      ((𝓞 F) ⧸ Q.under (𝓞 F)) ((𝓞 E) ⧸ Q) := by
    ext x
    simp only [H.restrict_apply, FiniteField.coe_frobeniusAlgHom, Nat.card_eq_fintype_card]
  rw [horder, hr, FiniteField.orderOf_frobeniusAlgHom,
    Ideal.inertiaDeg_eq_of_isMaximal (Q.under (𝓞 F)) Q]

end PrimeDegreePackets.GaloisIdealCharacter

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_PrimeFactors
attribute [-instance] _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
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
attribute [-instance] _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
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
attribute [-instance] _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
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
attribute [-instance] _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
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


end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_RayFrobenius
attribute [-instance] _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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

end GaloisIdealCharacter
end PrimeDegreePackets

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_ArtinEuler
attribute [-instance] _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Module
open scoped NumberField Classical BigOperators
namespace PrimeDegreePackets.GaloisIdealCharacter

lemma prod_one_sub_rootsOfUnity (n : ℕ) (hn : 0 < n) (z : ℂ) :
    letI : NeZero n := ⟨hn.ne'⟩
    letI : Fintype (rootsOfUnity n ℂ) := Fintype.ofFinite _
    (∏ ζ : rootsOfUnity n ℂ, (1 - (ζ.val : ℂ) * z)) = 1 - z ^ n := by
  let : NeZero n := ⟨hn.ne'⟩
  let : Fintype (rootsOfUnity n ℂ) := Fintype.ofFinite _
  obtain ⟨a, ha⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot ℂ n
  let ζ : rootsOfUnity n ℂ := ha.toRootsOfUnity
  have hcoe : (ζ.val : ℂ) = a := rfl
  let e : Fin n ≃ rootsOfUnity n ℂ := Equiv.ofBijective (fun i => ζ ^ i.val) (by
    constructor
    · intro i j hij
      apply Fin.ext
      apply ha.pow_inj i.isLt j.isLt
      have := congrArg (fun x : rootsOfUnity n ℂ => (x.val : ℂ)) hij
      simpa only [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hcoe] using this
    · intro b
      have hb : (b.val : ℂ)^n = 1 := by
        simpa only [Units.val_pow_eq_pow_val, Units.val_one] using
          congrArg Units.val ((mem_rootsOfUnity n b.val).mp b.property)
      obtain ⟨i, hi, hbi⟩ := ha.eq_pow_of_pow_eq_one hb
      refine ⟨⟨i, hi⟩, ?_⟩
      apply Subtype.ext
      apply Units.ext
      simpa only [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hcoe] using hbi)
  have hp := congrArg (Polynomial.eval (1 : ℂ))
    (X_pow_sub_C_eq_prod ha hn (rfl : z ^ n = z ^ n))
  simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_C, one_pow, Polynomial.eval_prod] at hp
  rw [hp, Finset.prod_range]
  exact (Fintype.prod_equiv e (fun i => 1 - a^i.val * z)
    (fun b => 1 - (b.val : ℂ) * z) (fun i => by
      change 1 - a^i.val * z = 1 - (ζ.val : ℂ)^i.val * z
      rw [hcoe])).symm

lemma zpowers_subtype_generator {G : Type*} [Group G] (g : G) :
    ∀ x : Subgroup.zpowers g,
      x ∈ Subgroup.zpowers (⟨g, Subgroup.mem_zpowers g⟩ : Subgroup.zpowers g) := by
  intro x
  obtain ⟨m, hm⟩ := x.property
  exact ⟨m, Subtype.ext hm⟩

lemma prod_characters_at_generator {H : Type*} [CommGroup H] [Finite H]
    (g : H) (hg : ∀ x : H, x ∈ Subgroup.zpowers g) (z : ℂ) :
    letI : Fintype (H →* ℂˣ) := Fintype.ofFinite _
    (∏ χ : H →* ℂˣ, (1 - (χ g : ℂ) * z)) = 1 - z ^ Nat.card H := by
  let : Fintype (H →* ℂˣ) := Fintype.ofFinite _
  let : Fintype (rootsOfUnity (Nat.card H) ℂ) := Fintype.ofFinite _
  let e := (IsCyclic.monoidHomMulEquivRootsOfUnityOfGenerator hg ℂˣ).trans
    (rootsOfUnityUnitsMulEquiv ℂ (Nat.card H))
  rw [← prod_one_sub_rootsOfUnity (Nat.card H) Nat.card_pos z]
  apply Fintype.prod_equiv e.toEquiv
  intro χ
  rfl

attribute [local instance] IsCyclic.commGroup

end PrimeDegreePackets.GaloisIdealCharacter

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_FrobeniusConductor
attribute [-instance] _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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

end PrimeDegreePackets

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_SplitEuler
attribute [-instance] _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue
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

end PrimeDegreePackets

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_FrobeniusCoset
attribute [-instance] _root_.AlgebraicNumberTheory.numberFieldInRationalSeparableClosure_numberField _root_.HilbertRamification.Dedekind.basePrime_isPrime _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.boundedRealFields_numberField _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.decompositionSubgroupMulSemiringAction _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedMaximalIdeal.instLiesOver _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.finiteNormalClosure_numberField _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Module
open scoped NumberField Pointwise Classical
namespace PrimeDegreePackets.GaloisIdealCharacter

variable (F E : Type*) [Field F] [NumberField F] [Field E] [NumberField E]
variable [Algebra F E] [FiniteDimensional F E] [IsGalois F E]

lemma zpowers_frobenius_eq_stabilizer
    (P : Ideal (𝓞 F)) (Q : Ideal (𝓞 E))
    [P.IsMaximal] [Q.IsMaximal] [Q.LiesOver P]
    [Algebra.IsUnramifiedAt (𝓞 F) Q]
    (g : E ≃ₐ[F] E) (hg : IsArithFrobAt (𝓞 F) g Q) :
    Subgroup.zpowers g = MulAction.stabilizer (E ≃ₐ[F] E) Q := by
  have hle : Subgroup.zpowers g ≤ MulAction.stabilizer (E ≃ₐ[F] E) Q :=
    Subgroup.zpowers_le.mpr hg.mem_stabilizer
  have hc : Nat.card (Subgroup.zpowers g) =
      Nat.card (MulAction.stabilizer (E ≃ₐ[F] E) Q) := by
    rw [Nat.card_zpowers, orderOf_eq_inertiaDeg_of_isArithFrobAt F E P Q g hg,
      Ideal.card_stabilizer_eq (G := E ≃ₐ[F] E) P Q,
      Ideal.ramificationIdxIn_eq_ramificationIdx P Q (E ≃ₐ[F] E),
      Ideal.inertiaDegIn_eq_inertiaDeg P Q (E ≃ₐ[F] E),
      Ideal.ramificationIdx_eq_one_of_isUnramifiedAt, one_mul]
  exact SetLike.coe_injective (Set.eq_of_inclusion_surjective
      ((Nat.bijective_iff_injective_and_card (Set.inclusion hle)).mpr
        ⟨Set.inclusion_injective hle, hc⟩).2)

attribute [local instance] OAI.PrimeDegreePackets.GaloisIdealCharacter.fixingRingGroup
attribute [local instance] OAI.PrimeDegreePackets.GaloisIdealCharacter.fixingRingCommutes
lemma primeOfCosetOrbit_bijective (L : IntermediateField F E) (P : Ideal (𝓞 F))
    (Q : Ideal (𝓞 E)) [P.IsPrime] [Q.IsPrime] [Q.LiesOver P] :
    Function.Bijective (primeOfCosetOrbit F E L P Q) := by
  constructor
  · intro a b
    induction a using Quotient.inductionOn
    rename_i a
    induction b using Quotient.inductionOn
    rename_i b
    intro hab
    apply Quotient.sound
    apply (cosetPrime_eq_iff F E L Q a b).mp
    exact congrArg Subtype.val hab
  · intro R
    let : R.val.IsPrime := R.property.1
    let : R.val.LiesOver P := R.property.2
    let S : Ideal.primesOver R.val (𝓞 E) := Classical.choice inferInstance
    let : S.val.IsPrime := S.property.1
    let : S.val.LiesOver R.val := S.property.2
    let : S.val.LiesOver P := Ideal.LiesOver.trans S.val R.val P
    obtain ⟨a, ha⟩ := Ideal.exists_smul_eq_of_isGaloisGroup P Q S.val (E ≃ₐ[F] E)
    refine ⟨Quotient.mk _ (QuotientGroup.mk a⁻¹), ?_⟩
    apply Subtype.ext
    change (a⁻¹⁻¹ • Q).under (𝓞 L) = R.val
    rw [inv_inv, ha]
    exact (S.val.over_def R.val).symm

lemma cosetOrbit_card_eq_inertiaDeg
    (L : IntermediateField F E) (P : Ideal (𝓞 F)) (hP : P ≠ ⊥)
    (Q : Ideal (𝓞 E)) [P.IsMaximal] [Q.IsMaximal] [Q.LiesOver P]
    [Algebra.IsUnramifiedAt (𝓞 F) Q] (a : E ≃ₐ[F] E) :
    Nat.card (MulAction.orbit (MulAction.stabilizer (E ≃ₐ[F] E) Q)
      (QuotientGroup.mk a : (E ≃ₐ[F] E) ⧸ L.fixingSubgroup)) =
      ((a⁻¹ • Q).under (𝓞 L)).inertiaDeg (𝓞 F) := by
  let Q' : Ideal (𝓞 E) := a⁻¹ • Q
  let R : Ideal (𝓞 L) := Q'.under (𝓞 L)
  let : Q'.IsPrime := Ideal.IsPrime.smul _
  let : Q'.LiesOver P := Ideal.LiesOver.smul _
  let : Q'.IsMaximal := Ideal.IsPrime.isMaximal inferInstance
    (Ideal.ne_bot_of_liesOver_of_ne_bot hP Q')
  let : R.IsPrime := inferInstance
  let : Q'.LiesOver R := inferInstance
  let : R.LiesOver P := by
    constructor
    rw [Ideal.under_under, Q'.over_def P]
  let : R.IsMaximal := Ideal.IsPrime.isMaximal inferInstance
    (Ideal.ne_bot_of_liesOver_of_ne_bot hP R)
  have heQ' : Q'.ramificationIdx (𝓞 F) = 1 := by
    change (a⁻¹ • Q).ramificationIdx (𝓞 F) = 1
    rw [Ideal.ramificationIdx_smul, Ideal.ramificationIdx_eq_one_of_isUnramifiedAt]
  have he : Q'.ramificationIdx (𝓞 L) = 1 := by
    have h := Ideal.ramificationIdx_tower (R := 𝓞 F) R Q'
    rw [heQ'] at h
    exact Nat.eq_one_of_mul_eq_one_left h.symm
  have hlocal : Nat.card (MulAction.stabilizer L.fixingSubgroup Q') =
      Q'.inertiaDeg (𝓞 L) := by
    have hc := Ideal.card_stabilizer_eq (G := L.fixingSubgroup) R Q'
    rw [Ideal.ramificationIdxIn_eq_ramificationIdx R Q' L.fixingSubgroup,
      Ideal.inertiaDegIn_eq_inertiaDeg R Q' L.fixingSubgroup, he, one_mul] at hc
    convert hc using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
  have hbase : Nat.card (MulAction.stabilizer (E ≃ₐ[F] E) Q) =
      Q.inertiaDeg (𝓞 F) := by
    rw [Ideal.card_stabilizer_eq (G := E ≃ₐ[F] E) P Q,
      Ideal.ramificationIdxIn_eq_ramificationIdx P Q (E ≃ₐ[F] E),
      Ideal.inertiaDegIn_eq_inertiaDeg P Q (E ≃ₐ[F] E),
      Ideal.ramificationIdx_eq_one_of_isUnramifiedAt, one_mul]
  have hstab := Nat.card_congr (cosetStabilizerEquiv L.fixingSubgroup Q a)
  have hc := Nat.card_congr
    (MulAction.orbitProdStabilizerEquivGroup (MulAction.stabilizer (E ≃ₐ[F] E) Q)
      (QuotientGroup.mk a : (E ≃ₐ[F] E) ⧸ L.fixingSubgroup))
  rw [Nat.card_prod, hstab, hlocal, hbase] at hc
  have hf : Q.inertiaDeg (𝓞 F) = R.inertiaDeg (𝓞 F) * Q'.inertiaDeg (𝓞 L) := by
    rw [← Ideal.inertiaDeg_smul (𝓞 F) Q a⁻¹]
    exact Ideal.inertiaDeg_tower R Q'
  apply Nat.eq_of_mul_eq_mul_right (Ideal.inertiaDeg_pos Q' (𝓞 L))
  exact hc.trans hf

 

theorem actual_frobenius_coset_cycle_lengths
    (L : IntermediateField F E) (P : Ideal (𝓞 F)) (hP : P ≠ ⊥)
    (Q : Ideal (𝓞 E)) [P.IsMaximal] [Q.IsMaximal] [Q.LiesOver P]
    [Algebra.IsUnramifiedAt (𝓞 F) Q]
    (g : E ≃ₐ[F] E) (hg : IsArithFrobAt (𝓞 F) g Q) :
    ∃ e : MulAction.orbitRel.Quotient (Subgroup.zpowers g)
        ((E ≃ₐ[F] E) ⧸ L.fixingSubgroup) ≃ Ideal.primesOver P (𝓞 L),
      ∀ o, Nat.card o.orbit = (e o).val.inertiaDeg (𝓞 F) := by
  rw [zpowers_frobenius_eq_stabilizer F E P Q g hg]
  refine ⟨Equiv.ofBijective (primeOfCosetOrbit F E L P Q)
    (primeOfCosetOrbit_bijective F E L P Q), ?_⟩
  intro o
  induction o using Quotient.inductionOn
  rename_i a
  induction a using Quotient.inductionOn
  rename_i a
  exact cosetOrbit_card_eq_inertiaDeg F E L P hP Q a

end PrimeDegreePackets.GaloisIdealCharacter

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_PermutationArtin
attribute [-instance] _root_.AlgebraicNumberTheory.numberFieldInRationalSeparableClosure_numberField _root_.HilbertRamification.Dedekind.basePrime_isPrime _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.finiteNormalClosure_numberField _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Module
open scoped NumberField Classical BigOperators
namespace PrimeDegreePackets.GaloisIdealCharacter

lemma det_eq_prod_of_eigenbasis {ι M : Type*} [Fintype ι] [AddCommGroup M]
    [Module ℂ M] (b : Basis ι ℂ M) (T : Module.End ℂ M) (a : ι → ℂ)
    (h : ∀ i, T (b i) = a i • b i) : T.det = ∏ i, a i := by
  rw [← LinearMap.det_toMatrix b]
  have he : LinearMap.toMatrix b b T = Matrix.diagonal a := by
    ext i j
    rw [LinearMap.toMatrix_apply', h j, map_smul]
    by_cases hij : i = j
    · subst j; simp
    · simp [hij]
  rw [he, Matrix.det_diagonal]

section OrbitFunctions
variable (C X : Type*) [CommGroup C] [Finite C] [MulAction C X] [Finite X]
local notation "Ω" => MulAction.orbitRel.Quotient C X
local notation "H" => orbitQuotient C X

attribute [local instance] OAI.PrimeDegreePackets.GaloisIdealCharacter.permutationArtinCharacterFintype
omit [Finite C] [Finite X] in
lemma orbitFunctionEquiv_translate (g : C) (f : X → ℂ) (o : Ω) (h : H o) :
    orbitFunctionEquiv C X (LinearEquiv.funCongrLeft ℂ ℂ (MulAction.toPerm g) f) o h =
      orbitFunctionEquiv C X f o ((g : H o) * h) := by
  simp only [orbitFunctionEquiv_apply]
  change f (g • MulAction.ofQuotientStabilizer C o.out h) =
    f (MulAction.ofQuotientStabilizer C o.out (g • h))
  rw [MulAction.ofQuotientStabilizer_smul]

attribute [local instance] OAI.PrimeDegreePackets.GaloisIdealCharacter.permutationArtinOrbitFintype
lemma orbitCharacterBasis_eigen (g : C) (j : (o : Ω) × (H o →* ℂˣ)) :
    let e := orbitFunctionEquiv C X
    (e.toLinearMap ∘ₗ (LinearEquiv.funCongrLeft ℂ ℂ (MulAction.toPerm g)).toLinearMap ∘ₗ
      e.symm.toLinearMap) (orbitCharacterBasis C X j) =
        (j.2 (g : H j.1) : ℂ) • orbitCharacterBasis C X j := by
  dsimp only
  ext o h
  change orbitFunctionEquiv C X
      (LinearEquiv.funCongrLeft ℂ ℂ (MulAction.toPerm g)
        ((orbitFunctionEquiv C X).symm (orbitCharacterBasis C X j))) o h = _
  rw [orbitFunctionEquiv_translate, LinearEquiv.apply_symm_apply]
  obtain ⟨a, χ⟩ := j
  by_cases hao : a = o
  · subst o
    simp [orbitCharacterBasis, Pi.basis_apply, map_mul]
  · simp [orbitCharacterBasis, Pi.basis_apply, hao]

omit [Finite C] [Finite X] in
lemma generator_quotient (g : C) (hg : ∀ c : C, c ∈ Subgroup.zpowers g)
    (o : Ω) : ∀ h : H o, h ∈ Subgroup.zpowers (g : H o) := by
  intro h
  induction h using Quotient.inductionOn
  rename_i c
  obtain ⟨m, hm⟩ := hg c
  exact ⟨m, by simpa using congrArg (QuotientGroup.mk' (MulAction.stabilizer C o.out)) hm⟩

lemma det_translate (g : C) (hg : ∀ c : C, c ∈ Subgroup.zpowers g) (z : ℂ) :
    (LinearMap.id - z • (LinearEquiv.funCongrLeft ℂ ℂ
      (MulAction.toPerm (β := X) g)).toLinearMap).det =
      ∏ o : Ω, (1 - z ^ Nat.card o.orbit) := by
  let e := orbitFunctionEquiv C X
  let T : Module.End ℂ (X → ℂ) := LinearMap.id - z •
    (LinearEquiv.funCongrLeft ℂ ℂ (MulAction.toPerm g)).toLinearMap
  rw [← LinearMap.det_conj T e]
  rw [det_eq_prod_of_eigenbasis (orbitCharacterBasis C X) _
    (fun j => 1 - (j.2 (g : H j.1) : ℂ) * z)]
  · rw [Fintype.prod_sigma]
    apply Finset.prod_congr rfl
    intro o _
    rw [prod_characters_at_generator _ (generator_quotient C X g hg o)]
    congr 2
    exact (Nat.card_congr (MulAction.orbitEquivQuotientStabilizer C o.out)).symm.trans
      (Nat.card_congr (Equiv.setCongr (MulAction.orbitRel.Quotient.orbit_eq_orbit_out
        o Quotient.out_eq')).symm)
  · intro j
    have h := orbitCharacterBasis_eigen C X g j
    change (e.toLinearMap ∘ₗ _ ∘ₗ e.symm.toLinearMap) _ = _ at h
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply,
      LinearMap.smul_apply, map_sub, map_smul, LinearEquiv.apply_symm_apply, T, LinearEquiv.coe_coe]
    rw [show e ((LinearEquiv.funCongrLeft ℂ ℂ (MulAction.toPerm g))
        (e.symm (orbitCharacterBasis C X j))) = _ from h]
    simp only [smul_smul, sub_smul, one_smul, mul_comm]

end OrbitFunctions

 

theorem actual_nonnormal_artin_localEuler
    (F E : Type*) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
    (L : IntermediateField F E) (P : Ideal (𝓞 F)) (hP : P ≠ ⊥)
    (Q : Ideal (𝓞 E)) [P.IsMaximal] [Q.IsMaximal] [Q.LiesOver P]
    [Algebra.IsUnramifiedAt (𝓞 F) Q]
    (g : E ≃ₐ[F] E) (hg : IsArithFrobAt (𝓞 F) g Q) (s : ℂ) :
    letI : Fintype (Ideal.primesOver P (𝓞 L)) := Fintype.ofFinite _
    (LinearMap.det (LinearMap.id - (Ideal.absNorm P : ℂ)^(-s) •
      (LinearEquiv.funCongrLeft ℂ ℂ
        (MulAction.toPerm (β := (E ≃ₐ[F] E) ⧸ L.fixingSubgroup) g⁻¹)).toLinearMap))⁻¹ =
      ∏ R : Ideal.primesOver P (𝓞 L), (1 - (Ideal.absNorm R.val : ℂ)^(-s))⁻¹ := by
  let : Fintype (Ideal.primesOver P (𝓞 L)) := Fintype.ofFinite _
  let C := Subgroup.zpowers g
  let X := (E ≃ₐ[F] E) ⧸ L.fixingSubgroup
  let c : C := ⟨g, Subgroup.mem_zpowers g⟩
  let : CommGroup C := IsCyclic.commGroup
  let : Fintype (MulAction.orbitRel.Quotient C X) := Fintype.ofFinite _
  have hgen : ∀ x : C, x ∈ Subgroup.zpowers c⁻¹ := by
    simpa only [Subgroup.zpowers_inv] using (zpowers_subtype_generator g)
  have hdet := det_translate C X c⁻¹ hgen ((Ideal.absNorm P : ℂ)^(-s))
  change (LinearMap.det (LinearMap.id - (Ideal.absNorm P : ℂ)^(-s) •
    (LinearEquiv.funCongrLeft ℂ ℂ (MulAction.toPerm (β := X) c⁻¹)).toLinearMap))⁻¹ = _
  rw [hdet, ← Finset.prod_inv_distrib]
  obtain ⟨e, he⟩ := actual_frobenius_coset_cycle_lengths F E L P hP Q g hg
  apply Fintype.prod_equiv e
  intro o
  rw [he o]
  have hnorm : Ideal.absNorm (e o).val =
      Ideal.absNorm P ^ (e o).val.inertiaDeg (𝓞 F) := by
    let R := e o
    let : R.val.IsPrime := R.property.1
    let : R.val.LiesOver P := R.property.2
    let : R.val.IsMaximal := R.property.1.isMaximal
      (Ideal.ne_bot_of_mem_primesOver hP R.property)
    exact (Ideal.absNorm_pow_inertiaDeg P R.val).symm
  rw [hnorm, Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul, Complex.cpow_nat_mul]

end PrimeDegreePackets.GaloisIdealCharacter

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_CosetMeromorphic
attribute [-instance] _root_.AlgebraicNumberTheory.numberFieldInRationalSeparableClosure_numberField _root_.HilbertRamification.Dedekind.basePrime_isPrime _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.finiteNormalClosure_numberField _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Module Filter Topology
open scoped NumberField Classical BigOperators
namespace PrimeDegreePackets.GaloisIdealCharacter

variable (F E : Type*) [Field F] [NumberField F] [Field E] [NumberField E]
variable [Algebra F E] [FiniteDimensional F E] [IsGalois F E]


lemma cosetRationalEuler_good (L : IntermediateField F E) {N : ℕ}
    (hD : (NumberField.discr E).natAbs ∣ N) (p : Nat.Primes) (hp : ¬ p.val ∣ N) (s : ℂ) :
    cosetRationalEuler F E L N p s = primeIdealEulerFactor L p.val s := by
  have hpD : p.val.Coprime (NumberField.discr E).natAbs :=
    (p.property.coprime_iff_not_dvd.mpr hp).of_dvd_right hD
  let (P : idealsOverPrime F p.val) : P.val.IsPrime :=
    ((mem_idealsOverPrime_iff F p.property.ne_zero P.val).mp P.property).1
  let (P : idealsOverPrime F p.val) : Fintype (Ideal.primesOver P.val (𝓞 L)) :=
    (Algebra.QuasiFinite.finite_primesOver P.val).fintype
  rw [cosetRationalEuler, ite_eq_right hp]
  unfold primeIdealEulerFactor
  rw [← (primeIdealTowerEquiv F L p.val p.property.ne_zero).prod_comp]
  simp only [primeIdealTowerEquiv_val, Fintype.prod_sigma]
  apply Finset.prod_congr rfl
  intro P _
  let PP := rationalPrimeSpectrum F p P
  let Q := primeAbove F E PP
  let : PP.asIdeal.IsMaximal := PP.isPrime.isMaximal PP.ne_bot
  let : Q.val.IsPrime := Q.property.1
  let : Q.val.IsMaximal := Q.property.1.isMaximal (primeAbove_ne_bot F E PP)
  let : Q.val.LiesOver PP.asIdeal := Q.property.2
  let : Algebra.IsUnramifiedAt (𝓞 F) Q.val :=
    unramified_of_absDiscr_not_mem F E PP.asIdeal Q.val Q.property.2.over.symm
      (Ideal.IsPrime.notMem_of_isCoprime_of_mem hpD.cast
        ((mem_idealsOverPrime_iff F p.property.ne_zero P.val).mp P.property).2)
  exact actual_nonnormal_artin_localEuler F E L PP.asIdeal PP.ne_bot Q.val
    (primeFrobenius F E PP) (primeFrobenius_spec F E PP) s

section EulerCorrection
variable (K : Type*) [Field K] [NumberField K]



lemma primeEuler_denominator_ne_zero {p : ℕ} (P : idealsOverPrime K p)
    {s : ℂ} (hs : 0 < s.re) : 1 - (Ideal.absNorm P.val : ℂ)^(-s) ≠ 0 := by
  have hn : 1 < (Ideal.absNorm P.val : ℝ) := by
    exact_mod_cast (idealsOverPrime_norm_two_le K P.property)
  have hnorm : ‖(Ideal.absNorm P.val : ℂ)^(-s)‖ < 1 := by
    rw [show (Ideal.absNorm P.val : ℂ) = ((Ideal.absNorm P.val : ℝ) : ℂ) by simp,
      Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    exact Real.rpow_lt_one_of_one_lt_of_neg hn (by simpa using neg_neg_of_pos hs)
  exact sub_ne_zero.mpr (fun h => by simp [← h] at hnorm)

end EulerCorrection

lemma cosetRationalEuler_hasProd_oai (L : IntermediateField F E) (N : ℕ) (hN : 0 < N)
    (hD : (NumberField.discr E).natAbs ∣ N) {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun p : Nat.Primes => cosetRationalEuler F E L N p s)
      (NumberField.dedekindZeta L s * removedEulerPolynomial L N s) := by
  let C : Nat.Primes → ℂ := fun p =>
    if p ∈ badRationalPrimes N then
      ∏ P : idealsOverPrime L p.val, (1 - (Ideal.absNorm P.val : ℂ)^(-s)) else 1
  have hC : HasProd C (removedEulerPolynomial L N s) := by
    have h : HasProd C (∏ p ∈ badRationalPrimes N, C p) := hasProd_prod_of_ne_finset_one (s := badRationalPrimes N) (f := C)
      (fun p hp => ite_eq_right hp)
    simpa only [C, Finset.prod_ite_mem, Finset.inter_self, removedEulerPolynomial] using h
  apply ((dedekindZeta_hasProd L hs).mul hC).congr_fun
  intro p
  have hpN : p ∈ badRationalPrimes N ↔ p.val ∣ N := by
    change (⟨p.val, p.property⟩ : Subtype Nat.Prime) ∈ N.primeFactors.subtype Nat.Prime ↔ _
    rw [Finset.mem_subtype, Nat.mem_primeFactors]
    exact ⟨fun h => h.2.1, fun h => ⟨p.property, h, hN.ne'⟩⟩
  by_cases hp : p.val ∣ N
  · simp only [cosetRationalEuler, ite_eq_left hp, C, ite_eq_left (hpN.mpr hp)]
    unfold primeIdealEulerFactor
    rw [← Finset.prod_mul_distrib]
    simp only [inv_mul_cancel₀ (primeEuler_denominator_ne_zero L _ (zero_lt_one.trans hs)),
      Finset.prod_const_one]
  · simp only [C, ite_eq_right (mt hpN.mp hp), mul_one]
    exact cosetRationalEuler_good F E L hD p hp s

open HeckeMellin

end PrimeDegreePackets.GaloisIdealCharacter

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.PrimeDegreePackets.GaloisIdealCharacter.cosetRationalEuler_hasProd_oai.{u_1, u_2} := @OAI.PrimeDegreePackets.GaloisIdealCharacter.cosetRationalEuler_hasProd_oai.{u_1, u_2}
