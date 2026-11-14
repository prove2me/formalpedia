-- Prove2me | solution 1 for OAI.PrimeDegreePackets.GaloisIdealCharacter.actual_cyclic_artin_factorization
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T06:42:23.479177+00:00
-- url     : https://prove2.me/submissions/91d8f99c-92d0-4038-8ee0-44d981f65b0b

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
attribute [-instance] _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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
-- module Solutions.OAIQ244_DUKE.PrimePackets_ArtinEuler
attribute [-instance] _root_.HilbertRamification.Dedekind.basePrime_isPrime _root_.LubinTate.compatibleGroupFamiliesCommGroup _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedMaximalIdeal.instIsMaximal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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

lemma prod_comp_surjective_hom {A B : Type*} [CommGroup A] [CommGroup B]
    [Fintype A] [Fintype B] (f : A →* B) (hf : Function.Surjective f) (v : B → ℂ) :
    (∏ a, v (f a)) = (∏ b, v b) ^ Nat.card f.ker := by
  rw [← Fintype.prod_fiberwise' f v, ← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro b _
  rw [Finset.prod_const, Finset.card_univ]
  congr 1
  exact (Fintype.card_eq_nat_card).trans
    (Nat.card_congr (MonoidHom.fiberEquivKerOfSurjective hf b))

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

lemma prod_characters_at_element {G : Type*} [CommGroup G] [Finite G]
    (g : G) (z : ℂ) :
    letI : Fintype (G →* ℂˣ) := Fintype.ofFinite _
    (∏ χ : G →* ℂˣ, (1 - (χ g : ℂ) * z)) =
      (1 - z ^ orderOf g) ^ Nat.card (G ⧸ Subgroup.zpowers g) := by
  let : Fintype (G →* ℂˣ) := Fintype.ofFinite _
  let H := Subgroup.zpowers g
  let : Fintype (H →* ℂˣ) := Fintype.ofFinite _
  let gH : H := ⟨g, Subgroup.mem_zpowers g⟩
  let r := MonoidHom.domRestrictHom H ℂˣ
  change (∏ χ : G →* ℂˣ, (1 - (r χ gH : ℂ) * z)) = _
  rw [prod_comp_surjective_hom r (MonoidHom.domRestrict_surjective (M := ℂ) H)
    (fun χ : H →* ℂˣ => 1 - (χ gH : ℂ) * z)]
  rw [prod_characters_at_generator gH (zpowers_subtype_generator g),
    CommGroup.card_domRestrictHom_ker (M := ℂ), Nat.card_zpowers]

variable (F E : Type*) [Field F] [NumberField F] [Field E] [NumberField E]
variable [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
variable [IsCyclic (E ≃ₐ[F] E)]
attribute [local instance] IsCyclic.commGroup



attribute [local instance] OAI.PrimeDegreePackets.GaloisIdealCharacter.artinCharacterFintype
attribute [local instance] OAI.PrimeDegreePackets.GaloisIdealCharacter.artinPrimesOverFintype
theorem actual_cyclic_artin_localEuler
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    [Algebra.IsUnramifiedAt (𝓞 F) (primeAbove F E P).val] (s : ℂ) :
    (∏ χ : (E ≃ₐ[F] E) →* ℂˣ,
      (1 - (χ (primeFrobenius F E P) : ℂ) * (Ideal.absNorm P.asIdeal : ℂ)^(-s))⁻¹) =
      ∏ Q : Ideal.primesOver P.asIdeal (𝓞 E),
        (1 - (Ideal.absNorm Q.val : ℂ)^(-s))⁻¹ := by
  let Q₀ := primeAbove F E P
  let : Q₀.val.IsPrime := Q₀.property.1
  let : Q₀.val.IsMaximal := Q₀.property.1.isMaximal (primeAbove_ne_bot F E P)
  let : Q₀.val.LiesOver P.asIdeal := Q₀.property.2
  let g := primeFrobenius F E P
  have ho : orderOf g = Q₀.val.inertiaDeg (𝓞 F) :=
    orderOf_eq_inertiaDeg_of_isArithFrobAt F E P.asIdeal Q₀.val g
      (primeFrobenius_spec F E P)
  have hcp : Nat.card (Ideal.primesOver P.asIdeal (𝓞 E)) * orderOf g = finrank F E := by
    have h := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
      P.asIdeal (𝓞 E) (E ≃ₐ[F] E)
    rw [Ideal.ramificationIdxIn_eq_ramificationIdx P.asIdeal Q₀.val (E ≃ₐ[F] E),
      Ideal.inertiaDegIn_eq_inertiaDeg P.asIdeal Q₀.val (E ≃ₐ[F] E),
      Ideal.ramificationIdx_eq_one_of_isUnramifiedAt, one_mul,
      IsGalois.card_aut_eq_finrank, ← ho] at h
    exact h
  have hcg : Nat.card ((E ≃ₐ[F] E) ⧸ Subgroup.zpowers g) * orderOf g = finrank F E := by
    rw [← Nat.card_zpowers g, ← Subgroup.card_eq_card_quotient_mul_card_subgroup,
      IsGalois.card_aut_eq_finrank]
  have hc : Nat.card ((E ≃ₐ[F] E) ⧸ Subgroup.zpowers g) =
      Nat.card (Ideal.primesOver P.asIdeal (𝓞 E)) := by
    exact Nat.eq_of_mul_eq_mul_right (orderOf_pos g) (hcg.trans hcp.symm)
  have hnorm (Q : Ideal.primesOver P.asIdeal (𝓞 E)) :
      Ideal.absNorm Q.val = Ideal.absNorm P.asIdeal ^ orderOf g := by
    let : Q.val.IsPrime := Q.property.1
    let : Q.val.LiesOver P.asIdeal := Q.property.2
    let : Q.val.IsMaximal := Q.property.1.isMaximal
      (Ideal.ne_bot_of_mem_primesOver P.ne_bot Q.property)
    rw [← Ideal.absNorm_pow_inertiaDeg P.asIdeal Q.val,
      ← Ideal.inertiaDeg_eq_of_isGaloisGroup P.asIdeal Q₀.val Q.val (E ≃ₐ[F] E), ho]
  have hfactor (Q : Ideal.primesOver P.asIdeal (𝓞 E)) :
      (Ideal.absNorm Q.val : ℂ)^(-s) = ((Ideal.absNorm P.asIdeal : ℂ)^(-s))^orderOf g := by
    rw [hnorm Q, Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul, Complex.cpow_nat_mul]
  rw [Finset.prod_inv_distrib, prod_characters_at_element]
  simp_rw [hfactor]
  rw [Finset.prod_const, Finset.card_univ, inv_pow, hc, Nat.card_eq_fintype_card]

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
-- module Solutions.OAIQ244_DUKE.PrimePackets_ArtinSeries
attribute [-instance] _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.finiteIdeleGroupT2Space _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Module Filter Topology
open scoped BigOperators NumberField nonZeroDivisors Classical
namespace PrimeDegreePackets.GaloisIdealCharacter
variable (F E : Type*) [Field F] [NumberField F] [Field E] [NumberField E]
variable [Algebra F E] [FiniteDimensional F E] [IsGalois F E]

namespace ArtinSeries
variable {F E} (χ : (E ≃ₐ[F] E) →* ℂˣ) (N : ℕ)

lemma idealHom_norm (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : ‖(idealHom F E χ I : ℂ)‖ = 1 := by
  obtain ⟨e, he, hpow⟩ := idealHom_finiteOrder F E χ
  apply (pow_eq_one_iff_of_nonneg (norm_nonneg _) he.ne').mp
  have H := congrArg (fun z : ℂˣ => ‖(z : ℂ)‖) (hpow I)
  simpa only [Units.val_pow_eq_pow_val, norm_pow, Units.val_one, norm_one] using H

lemma allCoefficient_norm_le_one (I : Ideal (𝓞 F)) : ‖allCoefficient χ N I‖ ≤ 1 := by
  unfold allCoefficient artinCoefficient
  split_ifs with hI hc
  · rw [idealHom_norm χ]
  · simp
  · simp

lemma idealTerm_apply {s : ℂ} (hs : 1 < s.re) (I : Ideal (𝓞 F)) :
    idealTerm χ N hs I = allCoefficient χ N I * (Ideal.absNorm I : ℂ)^(-s) := rfl

 

lemma idealNorm_summable {s : ℂ} (hs : 1 < s.re) :
    Summable (fun I : Ideal (𝓞 F) => ‖(Ideal.absNorm I : ℂ)^(-s)‖) := by
  let H := riemannZetaSummandHom (Complex.ne_zero_of_one_lt_re hs)
  have hz : (0 : ℂ)^(-s) = 0 := Complex.zero_cpow (neg_ne_zero.mpr (Complex.ne_zero_of_one_lt_re hs))
  have hf (m : ℕ) :
      (∑' I : {I : Ideal (𝓞 F) // Ideal.absNorm I = m}, ‖(Ideal.absNorm I.val : ℂ)^(-s)‖) =
        ‖LSeries.term (fun k => (idealCoefficientReal F k : ℂ)) s m‖ := by
    simp only [show ∀ I : {I : Ideal (𝓞 F) // Ideal.absNorm I = m},
      Ideal.absNorm I.val = m from fun I => I.property]
    by_cases hm : m = 0
    · subst m
      simp only [Nat.cast_zero, hz, norm_zero, tsum_zero, LSeries.term_zero]
    · rw [tsum_const, nsmul_eq_mul, LSeries.term_of_ne_zero hm, norm_div,
        idealCoefficientReal, ArithmeticFunction.coe_mk,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _),
        idealCoefficient_pos F m hm, Complex.cpow_neg, norm_inv, div_eq_mul_inv]
  apply (summable_partition (fun I => norm_nonneg ((Ideal.absNorm I : ℂ)^(-s)))
    (s := fun m => {I : Ideal (𝓞 F) | Ideal.absNorm I = m})
    (fun I => ⟨Ideal.absNorm I, rfl, fun _ hx => hx.symm⟩)).mpr
  refine ⟨fun m => ?_, ?_⟩
  · have : Finite {I : Ideal (𝓞 F) // Ideal.absNorm I = m} :=
      (Ideal.finite_setOfPred_absNorm_eq m).to_subtype
    let : Fintype {I : Ideal (𝓞 F) // Ideal.absNorm I = m} := Fintype.ofFinite _
    change Summable (fun I : {I : Ideal (𝓞 F) // Ideal.absNorm I = m} =>
      ‖(Ideal.absNorm I.val : ℂ)^(-s)‖)
    exact (hasSum_fintype _).summable
  · change Summable (fun m : ℕ => ∑' I : {I : Ideal (𝓞 F) // Ideal.absNorm I = m},
      ‖(Ideal.absNorm I.val : ℂ)^(-s)‖)
    simpa only [hf] using (idealCoefficient_LSeriesSummable F hs).norm

lemma idealTerm_summable {s : ℂ} (hs : 1 < s.re) : Summable (idealTerm χ N hs) := by
  apply Summable.of_norm_bounded (idealNorm_summable (F := F) hs)
  intro I
  rw [idealTerm_apply, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (allCoefficient_norm_le_one χ N I)

lemma normTerm_zero {s : ℂ} (hs : 1 < s.re) : normTerm χ N hs 0 = 0 := by
  unfold normTerm
  have H : ∀ I : {I : Ideal (𝓞 F) // Ideal.absNorm I = 0}, idealTerm χ N hs I.val = 0 := by
    intro I
    rw [Ideal.absNorm_eq_zero_iff.mp I.property]
    exact map_zero _
  simp only [H, tsum_zero]

lemma normTerm_one {s : ℂ} (hs : 1 < s.re) : normTerm χ N hs 1 = 1 := by
  let oneI : {I : Ideal (𝓞 F) // Ideal.absNorm I = 1} := ⟨⊤, Ideal.absNorm_top⟩
  have h : ∀ I : {I : Ideal (𝓞 F) // Ideal.absNorm I = 1}, I = oneI := by
    intro I
    exact Subtype.ext (Ideal.absNorm_eq_one_iff.mp I.property)
  rw [normTerm, tsum_eq_single oneI (fun I hI => (hI (h I)).elim)]
  change idealTerm χ N hs (⊤ : Ideal (𝓞 F)) = 1
  rw [← Ideal.one_eq_top]
  exact map_one (idealTerm χ N hs)

lemma normTerm_summable {s : ℂ} (hs : 1 < s.re) : Summable (normTerm χ N hs) := by
  exact ((idealTerm_summable χ N hs).hasSum.tsum_fiberwise Ideal.absNorm).summable

lemma normTerm_tsum {s : ℂ} (hs : 1 < s.re) :
    (∑' m : ℕ, normTerm χ N hs m) = artinDirichlet F E χ N s := by
  change (∑' m : ℕ, normTerm χ N hs m) = ∑' I : Ideal (𝓞 F), idealTerm χ N hs I
  exact ((idealTerm_summable χ N hs).hasSum.tsum_fiberwise Ideal.absNorm).tsum_eq

lemma normTerm_mul {s : ℂ} (hs : 1 < s.re) {m n : ℕ} (hc : m.Coprime n) :
    normTerm χ N hs (m*n) = normTerm χ N hs m * normTerm χ N hs n := by
  by_cases hm : m = 0
  · simp [hm, normTerm_zero χ N hs]
  by_cases hn : n = 0
  · simp [hn, normTerm_zero χ N hs]
  unfold normTerm
  rw [← (idealNormProductEquiv F m n hm hn hc).tsum_eq]
  change (∑' IJ : {I : Ideal (𝓞 F) // Ideal.absNorm I = m} ×
      {J : Ideal (𝓞 F) // Ideal.absNorm J = n}, idealTerm χ N hs (IJ.1.val * IJ.2.val)) = _
  simp only [map_mul]
  exact (tsum_mul_tsum_of_summable_norm
    ((idealTerm_summable χ N hs).subtype _).norm
    ((idealTerm_summable χ N hs).subtype _).norm).symm

lemma prime_idealTerm_norm_lt_one {s : ℂ} (hs : 1 < s.re) {p : ℕ}
    (P : idealsOverPrime F p) : ‖idealTerm χ N hs P.val‖ < 1 := by
  have H := zetaSummand_norm_lt_one hs (idealsOverPrime_norm_two_le F P.property)
  change ‖allCoefficient χ N P.val *
    riemannZetaSummandHom (Complex.ne_zero_of_one_lt_re hs) (Ideal.absNorm P.val)‖ < 1
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (allCoefficient_norm_le_one χ N P.val)).trans_lt H

 

theorem primary_ideal_euler {s : ℂ} (hs : 1 < s.re) {p : ℕ} :
    (∑' I : PrimaryIdeal F p, idealTerm χ N hs I.val) =
      ∏ P : idealsOverPrime F p, (1 - idealTerm χ N hs P.val)⁻¹ := by
  have HM (m : Multiset (idealsOverPrime F p)) :
      idealTerm χ N hs (primaryIdealMultisetEquiv F p m).val =
        (m.map (fun P => idealTerm χ N hs P.val)).prod := by
    rw [primaryIdealMultisetEquiv_val]
    induction m using Multiset.induction_on with
    | empty => exact map_one _
    | @cons P m ih =>
      simp only [Multiset.map_cons, Multiset.prod_cons, map_mul]
      exact congrArg (fun z => idealTerm χ N hs P.val * z) ih
  have HT := (complex_tsum_multiset_prod (fun P : idealsOverPrime F p =>
    idealTerm χ N hs P.val) (prime_idealTerm_norm_lt_one χ N hs)).2
  rw [← (primaryIdealMultisetEquiv F p).tsum_eq]
  exact (tsum_congr HM).trans HT

theorem local_euler {s : ℂ} (hs : 1 < s.re) {p : ℕ} (hp : p.Prime) :
    (∑' e : ℕ, normTerm χ N hs (p^e)) =
      ∏ P : idealsOverPrime F p, (1 - idealTerm χ N hs P.val)⁻¹ := by
  have HS : Summable (fun I : PrimaryIdeal F p => idealTerm χ N hs I.val) :=
    (idealTerm_summable χ N hs).subtype _
  have HE := (primaryIdealNormEquiv F p hp).summable_iff.mpr HS
  calc
    _ = ∑' I : Σ e : ℕ, {I : Ideal (𝓞 F) // Ideal.absNorm I = p^e},
        idealTerm χ N hs I.2.val := HE.tsum_sigma.symm
    _ = ∑' I : PrimaryIdeal F p, idealTerm χ N hs I.val :=
      (primaryIdealNormEquiv F p hp).tsum_eq (fun I => idealTerm χ N hs I.val)
    _ = _ := primary_ideal_euler χ N hs

 
theorem dirichlet_hasProd {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun p : Nat.Primes =>
      ∏ P : idealsOverPrime F (p:ℕ), (1 - idealTerm χ N hs P.val)⁻¹) (artinDirichlet F E χ N s) := by
  have HE := EulerProduct.eulerProduct_hasProd (normTerm_one χ N hs)
    (fun h => normTerm_mul χ N hs h) (normTerm_summable χ N hs).norm (normTerm_zero χ N hs)
  rw [normTerm_tsum χ N hs] at HE
  have he : (fun p : Nat.Primes => ∑' e : ℕ, normTerm χ N hs ((p:ℕ)^e)) =
      (fun p : Nat.Primes => ∏ P : idealsOverPrime F (p:ℕ),
        (1 - idealTerm χ N hs P.val)⁻¹) := by
    funext p
    exact local_euler χ N hs p.property
  rwa [he] at HE

end ArtinSeries
end PrimeDegreePackets.GaloisIdealCharacter

namespace PrimeDegreePackets.GaloisIdealCharacter
variable (F E : Type*) [Field F] [NumberField F] [Field E] [NumberField E]
variable [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
namespace ArtinSeries
lemma local_euler_bad (χ : (E ≃ₐ[F] E) →* ℂˣ) {N : ℕ}
    (p : Nat.Primes) (hpN : p.val ∣ N) {s : ℂ} (hs : 1 < s.re) :
    (∏ P : idealsOverPrime F p.val, (1 - idealTerm χ N hs P.val)⁻¹) = 1 := by
  apply Finset.prod_eq_one
  intro P _
  have hP := (mem_idealsOverPrime_iff F p.property.ne_zero P.val).mp P.property
  have hc : ¬ IsCoprime P.val (ThetaConstruction.rationalModulusIdeal (𝓞 F) N) := by
    intro hc
    have hNm : (N : 𝓞 F) ∈ P.val := by
      obtain ⟨k, rfl⟩ := hpN
      rw [Nat.cast_mul]
      exact P.val.mul_mem_right _ hP.2
    have hle : ThetaConstruction.rationalModulusIdeal (𝓞 F) N ≤ P.val :=
      (Ideal.span_singleton_le_iff_mem _).mpr hNm
    apply hP.1.ne_top'
    apply eq_top_iff.mpr
    rw [← hc.codisjoint.eq_top]
    exact sup_le le_rfl hle
  have hz : artinCoefficient F E χ N P.val = 0 := by
    unfold artinCoefficient
    split
    · simp
    · rfl
  simp only [idealTerm_apply, allCoefficient, hz, zero_mul, sub_zero, inv_one]

variable [IsCyclic (E ≃ₐ[F] E)]
attribute [local instance] IsCyclic.commGroup

attribute [local instance] OAI.PrimeDegreePackets.GaloisIdealCharacter.ArtinSeries.instFintypeMonoidHomAlgEquivUnitsComplex_solutions
lemma local_euler_good {N : ℕ} (hD : (NumberField.discr E).natAbs ∣ N)
    (p : Nat.Primes) (hpN : ¬ p.val ∣ N) {s : ℂ} (hs : 1 < s.re) :
    (∏ χ : (E ≃ₐ[F] E) →* ℂˣ,
      ∏ P : idealsOverPrime F p.val, (1 - idealTerm χ N hs P.val)⁻¹) =
        primeIdealEulerFactor E p.val s := by
  have hpC : p.val.Coprime N := p.property.coprime_iff_not_dvd.mpr hpN
  have hpD : p.val.Coprime (NumberField.discr E).natAbs :=
    hpC.of_dvd_right hD
  let (P : idealsOverPrime F p.val) : P.val.IsPrime :=
    ((mem_idealsOverPrime_iff F p.property.ne_zero P.val).mp P.property).1
  let (P : idealsOverPrime F p.val) : Fintype (Ideal.primesOver P.val (𝓞 E)) :=
    (Algebra.QuasiFinite.finite_primesOver P.val).fintype
  rw [Finset.prod_comm]
  unfold primeIdealEulerFactor
  rw [← (primeIdealTowerEquiv F E p.val p.property.ne_zero).prod_comp]
  simp only [primeIdealTowerEquiv_val, Fintype.prod_sigma]
  apply Finset.prod_congr rfl
  intro P _
  have hP := (mem_idealsOverPrime_iff F p.property.ne_zero P.val).mp P.property
  have hP0 : P.val ≠ ⊥ := by
    intro he
    rw [he, Ideal.mem_bot] at hP
    exact p.property.ne_zero (Nat.cast_eq_zero.mp hP.2)
  let PP : IsDedekindDomain.HeightOneSpectrum (𝓞 F) := ⟨P.val, hP.1, hP0⟩
  have hc : IsCoprime P.val (ThetaConstruction.rationalModulusIdeal (𝓞 F) N) := by
    apply Ideal.isCoprime_iff_codisjoint.mpr
    apply Codisjoint.mono ((Ideal.span_singleton_le_iff_mem _).mpr hP.2) le_rfl
    exact ((Ideal.isCoprime_span_singleton_iff _ _).mpr hpC.cast).codisjoint
  let Q := primeAbove F E PP
  let : Q.val.IsPrime := Q.property.1
  let : Algebra.IsUnramifiedAt (𝓞 F) (primeAbove F E PP).val :=
    unramified_of_absDiscr_not_mem F E PP.asIdeal Q.val Q.property.2.over.symm
      (Ideal.IsPrime.notMem_of_isCoprime_of_mem hpD.cast hP.2)
  have he (χ : (E ≃ₐ[F] E) →* ℂˣ) :
      idealTerm χ N hs P.val =
        (χ (primeFrobenius F E PP) : ℂ) * (Ideal.absNorm P.val : ℂ)^(-s) := by
    rw [idealTerm_apply]
    change artinCoefficient F E χ N PP.asIdeal * _ = _
    have hc' : IsCoprime PP.asIdeal (ThetaConstruction.rationalModulusIdeal (𝓞 F) N) := hc
    rw [artinCoefficient, dite_eq_left PP.ne_bot, ite_eq_left hc', idealHom_prime]
  simp only [he]
  exact actual_cyclic_artin_localEuler F E PP s
end ArtinSeries
end PrimeDegreePackets.GaloisIdealCharacter

namespace PrimeDegreePackets.GaloisIdealCharacter
variable (F E : Type*) [Field F] [NumberField F] [Field E] [NumberField E]
variable [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
variable [IsCyclic (E ≃ₐ[F] E)]
attribute [local instance] IsCyclic.commGroup



attribute [local instance] OAI.PrimeDegreePackets.GaloisIdealCharacter.artinSeriesCharacterFintype
theorem actual_cyclic_artin_factorization_oai (N : ℕ) (hN : 0 < N)
    (hD : (NumberField.discr E).natAbs ∣ N) {s : ℂ} (hs : 1 < s.re) :
    NumberField.dedekindZeta E s =
      (∏ p ∈ badRationalPrimes N, primeIdealEulerFactor E p.val s) *
        ∏ χ : (E ≃ₐ[F] E) →* ℂˣ, artinDirichlet F E χ N s := by
  let C : Nat.Primes → ℂ := fun p =>
    if p ∈ badRationalPrimes N then primeIdealEulerFactor E p.val s else 1
  have hC : HasProd C (∏ p ∈ badRationalPrimes N, primeIdealEulerFactor E p.val s) := by
    have h : HasProd C (∏ p ∈ badRationalPrimes N, C p) := hasProd_prod_of_ne_finset_one
      (s := badRationalPrimes N) (f := C) (fun p hp => ite_eq_right hp)
    simpa only [C, Finset.prod_ite_mem, Finset.inter_self] using h
  have hA := hasProd_prod (s := (Finset.univ : Finset ((E ≃ₐ[F] E) →* ℂˣ)))
    (fun χ _ => ArtinSeries.dirichlet_hasProd (F := F) (E := E) χ N hs)
  have hprod := hC.mul hA
  have he (p : Nat.Primes) :
      primeIdealEulerFactor E p.val s =
        C p * ∏ χ : (E ≃ₐ[F] E) →* ℂˣ,
          ∏ P : idealsOverPrime F p.val, (1 - ArtinSeries.idealTerm χ N hs P.val)⁻¹ := by
    have hmem : p ∈ badRationalPrimes N ↔ p.val ∣ N := by
      change (⟨p.val, p.property⟩ : Subtype Nat.Prime) ∈
        N.primeFactors.subtype Nat.Prime ↔ p.val ∣ N
      rw [Finset.mem_subtype, Nat.mem_primeFactors]
      exact ⟨fun h => h.2.1, fun h => ⟨p.property, h, hN.ne'⟩⟩
    by_cases hp : p.val ∣ N
    · simp only [C, ite_eq_left (hmem.mpr hp), ArtinSeries.local_euler_bad F E _ p hp hs,
        Finset.prod_const_one, mul_one]
    · dsimp only [C]
      rw [ite_eq_right (mt hmem.mp hp), one_mul]
      exact (ArtinSeries.local_euler_good F E hD p hp hs).symm
  exact (dedekindZeta_hasProd E hs).unique (hprod.congr_fun he)
end PrimeDegreePackets.GaloisIdealCharacter

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.PrimeDegreePackets.GaloisIdealCharacter.actual_cyclic_artin_factorization_oai.{u_1, u_2} := @OAI.PrimeDegreePackets.GaloisIdealCharacter.actual_cyclic_artin_factorization_oai.{u_1, u_2}
