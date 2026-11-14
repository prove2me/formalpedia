-- Prove2me | solution 1 for OAI.DukePrimeDegree.completedXiGap_of_exceptionalRealZeroExclusion
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T06:50:01.869675+00:00
-- url     : https://prove2.me/submissions/289dcdba-34c9-4fde-8582-e85dbafc4e9b

import Mathlib
import Mathlib.Algebra.Module.Submodule.RestrictScalars
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.RingTheory.Discriminant
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.Localization.Module
import Definitions.Def_DukePrimeDegree
import Definitions.Def_OAIQ244Duke023
import Definitions.Def_OAIQ244Duke024
import Theorems.Thm_OAI_PrimeDegreePackets_HeckeMellin_completedThetaXi_conj_totallyReal
import Theorems.Thm_OAI_PrimeDegreePackets_HeckeMellin_completedThetaXi_entire
import Theorems.Thm_OAI_PrimeDegreePackets_HeckeMellin_completedThetaXi_eq_totallyReal
import Theorems.Thm_OAI_PrimeDegreePackets_HeckeMellin_completedThetaXi_functionalEquation_totallyReal
import Theorems.Thm_OAI_PrimeDegreePackets_HeckeMellin_completedThetaXi_hasSubquadraticGrowth
import Theorems.Thm_OAI_PrimeDegreePackets_HeckeMellin_completedThetaXi_logDeriv_base_le_totallyReal
import Theorems.Thm_OAI_PrimeDegreePackets_HeckeMellin_dedekindXiZeros_ne_one_totallyReal
import Theorems.Thm_OAI_PrimeDegreePackets_HeckeMellin_dedekindXiZeros_ne_zero_totallyReal

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
-- module Solutions.OAIQ244_DUKE.PrimePackets_ZetaDerivatives
attribute [-instance] _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space
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
-- module Solutions.OAIQ244_DUKE.PrimePackets_RootOverlaps
attribute [-instance] _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.finiteIdeleGroupT2Space _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.OAI.PrimeDegreePackets.totallyRealCompletedXi_one
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

lemma totallyRealCompletedXi_ne_zero (K : Type*) [Field K] [NumberField K]
    {s : ℂ} (hs : 1 < s.re) : totallyRealCompletedXi K s ≠ 0 := by
  have hs0 : s ≠ 0 := Complex.ne_zero_of_one_lt_re hs
  have hs1 : s-1 ≠ 0 := by
    intro he
    have hr := congrArg Complex.re (sub_eq_zero.mp he)
    simp [hr] at hs
  unfold totallyRealCompletedXi
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hs0 hs1)
    (completionExponential_ne_zero _ _ _))
    (pow_ne_zero _ (Complex.Gamma_ne_zero (half_ne_nonpositive_integer (by linarith)))))
    (dedekindZeta_ne_zero_of_one_lt_re K hs)

end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_AnalyticLogarithms
attribute [-instance] _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction_continuous _root_.OAI.PrimeDegreePackets.instContinuousSMulPadicLocalAlgebra _root_.OAI.PrimeDegreePackets.instIsModuleTopologyPadicLocalAlgebra _root_.OAI.PrimeDegreePackets.instIsTopologicalRingLocalAlgebra _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.xT2Space _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.finiteIdeleGroupT2Space _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space
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
namespace PrimeDegreePackets.AnalyticGrowth

 

lemma exists_disk_logarithm {g : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hg : DifferentiableOn ℂ g (ball 0 R))
    (hzero : ∀ z ∈ ball 0 R, g z ≠ 0) :
    ∃ h : ℂ → ℂ, h 0 = 0 ∧
      (∀ z ∈ ball 0 R, HasDerivAt h (logDeriv g z) z) ∧
      (∀ z ∈ ball 0 R, Complex.exp (h z) = g z / g 0) := by
  have hga : AnalyticOnNhd ℂ g (ball 0 R) := hg.analyticOnNhd isOpen_ball
  have hld : DifferentiableOn ℂ (logDeriv g) (ball 0 R) := by
    intro z hz
    exact (((hga z hz).deriv.differentiableAt).div
      ((hg z hz).differentiableAt (isOpen_ball.mem_nhds hz)) (hzero z hz)).differentiableWithinAt
  obtain ⟨h,h0,hh⟩ := hld.isExactOn_ball.with_val_at 0 0
  refine ⟨h,h0,hh,?_⟩
  have HD : ∀ z ∈ ball 0 R,
      HasDerivAt (fun z => g z * Complex.exp (-h z)) 0 z := by
    intro z hz
    have H := ((hg z hz).differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt.mul ((hh z hz).neg.cexp)
    apply H.congr_deriv
    dsimp only [Pi.neg_apply, logDeriv_apply]
    field_simp [hzero z hz]
    ring
  have HE : EqOn (fun z => g z * Complex.exp (-h z)) (fun _ => g 0) (ball 0 R) := by
    apply isOpen_ball.eqOn_of_deriv_eq (convex_ball (0:ℂ) R).isPreconnected
      (fun z hz => (HD z hz).differentiableAt.differentiableWithinAt)
      (differentiableOn_const _) (fun z hz => by rw [(HD z hz).deriv, deriv_const])
      (mem_ball_self hR)
    simp [h0]
  intro z hz
  have H := HE hz
  rw [eq_div_iff (hzero 0 (mem_ball_self hR))]
  have He : Complex.exp (-h z) * Complex.exp (h z) = 1 := by
    rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
  have HH := congrArg (fun w => w*Complex.exp (h z)) H
  rw [mul_assoc, He, mul_one] at HH
  exact (mul_comm _ _).trans HH.symm

lemma disk_logarithm_re {g h : ℂ → ℂ} {z : ℂ}
    (hzero : g 0 ≠ 0) (hz : Complex.exp (h z) = g z / g 0) :
    (h z).re = Real.log ‖g z‖ - Real.log ‖g 0‖ := by
  have Hg : g z ≠ 0 := by
    intro H
    rw [H, zero_div] at hz
    exact Complex.exp_ne_zero _ hz
  have H := congrArg (fun w : ℂ => Real.log ‖w‖) hz
  simpa only [Complex.norm_exp, Real.log_exp, norm_div,
    Real.log_div (norm_ne_zero_iff.mpr Hg) (norm_ne_zero_iff.mpr hzero)] using H

end PrimeDegreePackets.AnalyticGrowth


namespace PrimeDegreePackets.AnalyticGrowth

 

lemma deriv_sub_le_of_re_le {h : ℂ → ℂ} {R M : ℝ} (hR : 0 < R) (hM : 0 < M)
    (hh : DifferentiableOn ℂ h (ball 0 R)) (h0 : h 0 = 0)
    (hreal : ∀ z ∈ ball 0 R, (h z).re ≤ M)
    {z w : ℂ} (hz : z ∈ Metric.ball 0 (R/4)) (hw : w ∈ Metric.ball 0 (R/4)) :
    ‖deriv h z - deriv h w‖ ≤ (64*M/R^2)*‖z-w‖ := by
  have HR4 : 0 < R/4 := by positivity
  have HE : ∀ a ∈ Metric.ball (0:ℂ) (R/4),
      closedBall a (R/4) ⊆ ball (0:ℂ) R := by
    intro a ha b hb
    rw [mem_ball_zero_iff] at ha ⊢
    have HB := norm_le_norm_sub_add b a
    have HH : ‖b-a‖ ≤ R/4 := by simpa [dist_eq_norm] using hb
    linarith
  have HB : ∀ a ∈ Metric.ball (0:ℂ) (R/4), ∀ b ∈ sphere a (R/4), ‖h b‖ ≤ 2*M := by
    intro a ha b hb
    have Hba : ‖b-a‖ = R/4 := by simpa [dist_eq_norm] using hb
    have Ha : ‖a‖ < R/4 := mem_ball_zero_iff.mp ha
    have Hb : ‖b‖ < R/2 := by linarith [norm_le_norm_sub_add b a]
    have HBR : b ∈ ball (0:ℂ) R := mem_ball_zero_iff.mpr (by linarith)
    have H := Complex.borelCaratheodory_zero hM hh (fun x hx => hreal x hx) hR HBR h0
    apply H.trans
    rw [div_le_iff₀ (by linarith : 0 < R-‖b‖)]
    nlinarith
  have H2 : ∀ a ∈ Metric.ball (0:ℂ) (R/4),
      ‖deriv (deriv h) a‖ ≤ 64*M/R^2 := by
    intro a ha
    have H := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
      2 HR4 (hh.diffContOnCl_ball (HE a ha)) (HB a ha)
    have HN : (2:ℝ)*(2*M)/(R/4)^2 = 64*M/R^2 := by ring
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero, Nat.factorial_two,
      Nat.cast_ofNat, HN] using H
  apply Convex.norm_image_sub_le_of_norm_deriv_le _ H2 (convex_ball (0:ℂ) (R/4)) hw hz
  intro a ha
  apply ((hh.analyticOnNhd isOpen_ball) a (HE a ha (mem_closedBall_self HR4.le))).deriv.differentiableAt

 

lemma logDeriv_sub_le_of_log_norm_le {g : ℂ → ℂ} {R M : ℝ}
    (hR : 0 < R) (hM : 0 < M) (hg : DifferentiableOn ℂ g (ball 0 R))
    (hzero : ∀ z ∈ ball 0 R, g z ≠ 0)
    (hbound : ∀ z ∈ ball 0 R, Real.log ‖g z‖ - Real.log ‖g 0‖ ≤ M)
    {z w : ℂ} (hz : z ∈ Metric.ball 0 (R/4)) (hw : w ∈ Metric.ball 0 (R/4)) :
    ‖logDeriv g z - logDeriv g w‖ ≤ (64*M/R^2)*‖z-w‖ := by
  obtain ⟨h,h0,hh,HE⟩ := exists_disk_logarithm hR hg hzero
  have hh' : DifferentiableOn ℂ h (ball 0 R) :=
    fun z hz => (hh z hz).differentiableAt.differentiableWithinAt
  have H := deriv_sub_le_of_re_le hR hM hh' h0 (fun z hz => by
    rw [disk_logarithm_re (hzero 0 (mem_ball_self hR)) (HE z hz)]
    exact hbound z hz) hz hw
  have hs : Metric.ball (0:ℂ) (R/4) ⊆ ball 0 R := ball_subset_ball (by linarith)
  rwa [(hh z (hs hz)).deriv, (hh w (hs hw)).deriv] at H

end PrimeDegreePackets.AnalyticGrowth

open Complex Set Metric Filter MeromorphicOn
namespace PrimeDegreePackets.AnalyticGrowth

lemma entire_order_ne_top {f : ℂ → ℂ} (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0)
    (z : ℂ) : meromorphicOrderAt f z ≠ ⊤ := by
  have HM : Meromorphic f := fun z => (hf.analyticAt z).meromorphicAt
  apply HM.exists_meromorphicOrderAt_ne_top_iff_forall.mp
  use 0
  rw [(hf.analyticAt 0).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr h0]
  simp

lemma divisor_sphere_eq_zero {f : ℂ → ℂ} {R : ℝ} (hf : Differentiable ℂ f)
    (hS : ∀ z ∈ sphere (0:ℂ) R, f z ≠ 0) : divisor f (sphere 0 R) = 0 := by
  ext z
  by_cases hz : z ∈ sphere (0:ℂ) R
  · rw [MeromorphicOn.divisor_apply (fun z _ => (hf.analyticAt z).meromorphicAt) hz,
      (hf.analyticAt z).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr (hS z hz)]
    simp
  · simp only [divisor_def, hz, and_false, ite_false, if_false, Function.locallyFinsuppWithin.coe_zero, Pi.zero_apply]

lemma exists_entire_ecanonicalDecomp {f : ℂ → ℂ} {R : ℝ}
    (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0) :
    ∃ g, ECanonicalDecomp f g R := by
  exact MeromorphicOn.exists_ecanonicalDecomp (fun z _ => (hf.analyticAt z).meromorphicAt)
    (fun z => entire_order_ne_top hf h0 z)

lemma ecanonical_log_norm_eq_on_sphere {f g : ℂ → ℂ} {R : ℝ}
    (D : ECanonicalDecomp f g R) (hf : Differentiable ℂ f) (hR : 0 < R)
    (hS : ∀ z ∈ sphere (0:ℂ) R, f z ≠ 0) {z : ℂ} (hz : z ∈ sphere (0:ℂ) R) :
    Real.log ‖g z‖ = Real.log ‖f z‖ := by
  rw [D.log_norm_eq (sphere_subset_closedBall hz)
    ((hf.analyticAt z).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr (hS z hz)) hR,
    (hf.analyticAt z).meromorphicTrailingCoeffAt_of_ne_zero (hS z hz),
    divisor_sphere_eq_zero hf hS]
  suffices (∑ᶠ i, (divisor f (ball (0:ℂ) R) i : ℝ) *
      Real.log ‖canonicalFactor R i z‖) = 0 by simp [this]
  trans ∑ᶠ _i : ℂ, (0:ℝ)
  · apply finsum_congr
    intro i
    by_cases hi : divisor f (ball (0:ℂ) R) i = 0
    · simp [hi]
    · have hiB := (divisor f (ball (0:ℂ) R)).supportWithinDomain hi
      rw [norm_canonicalFactor_eval_circle_eq_one hiB hz, Real.log_one, mul_zero]
  · exact finsum_zero

lemma norm_canonicalFactor_zero {R : ℝ} {i : ℂ} (hR : 0 < R) :
    ‖canonicalFactor R i 0‖ = R/‖i‖ := by
  simp only [canonicalFactor_apply, mul_zero, sub_zero, zero_sub, norm_div,
    norm_pow, norm_real, Real.norm_eq_abs, abs_of_pos hR, norm_mul, norm_neg]
  by_cases hi : i = 0
  · simp [hi]
  · field_simp

lemma ecanonical_log_norm_zero_ge {f g : ℂ → ℂ} {R : ℝ}
    (D : ECanonicalDecomp f g R) (hf : Differentiable ℂ f) (hR : 0 < R)
    (hS : ∀ z ∈ sphere (0:ℂ) R, f z ≠ 0) (h0 : f 0 ≠ 0) :
    Real.log ‖f 0‖ ≤ Real.log ‖g 0‖ := by
  rw [D.log_norm_eq (mem_closedBall_self hR.le)
    ((hf.analyticAt 0).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr h0) hR,
    (hf.analyticAt 0).meromorphicTrailingCoeffAt_of_ne_zero h0,
    divisor_sphere_eq_zero hf hS]
  simp only [Function.locallyFinsuppWithin.coe_zero, Pi.zero_apply, Int.cast_zero, zero_mul,
    finsum_zero, sub_zero, le_add_iff_nonneg_left]
  apply finsum_nonneg
  intro i
  by_cases hi : divisor f (ball (0:ℂ) R) i = 0
  · simp [hi]
  have hiB := (divisor f (ball (0:ℂ) R)).supportWithinDomain hi
  have hi0 : i ≠ 0 := by
    intro H
    subst i
    rw [MeromorphicOn.divisor_apply (fun z _ => (hf.analyticAt z).meromorphicAt)
      (mem_ball_self hR), (hf.analyticAt 0).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr h0] at hi
    simp at hi
  apply mul_nonneg
  · exact_mod_cast AnalyticOnNhd.divisor_nonneg (fun z _ => hf.analyticAt z) i
  · rw [norm_canonicalFactor_zero hR]
    apply Real.log_nonneg
    apply (le_div_iff₀ (norm_pos_iff.mpr hi0)).mpr
    simpa using (mem_ball_zero_iff.mp hiB).le

lemma ecanonical_log_norm_le {f g : ℂ → ℂ} {R B : ℝ}
    (D : ECanonicalDecomp f g R) (hf : Differentiable ℂ f) (hR : 0 < R)
    (hS : ∀ z ∈ sphere (0:ℂ) R, f z ≠ 0)
    (hbound : ∀ z ∈ sphere (0:ℂ) R, ‖f z‖ ≤ Real.exp B)
    {z : ℂ} (hz : z ∈ closedBall (0:ℂ) R) : Real.log ‖g z‖ ≤ B := by
  apply (Real.log_le_iff_le_exp (norm_pos_iff.mpr (D.ne_zero z hz))).mpr
  apply Complex.norm_le_of_forall_mem_frontier_norm_le (isBounded_ball (x := (0:ℂ)) (r := R))
    (D.analyticOnNhd.differentiableOn.diffContOnCl_ball subset_rfl)
  · intro w hw
    have hwS : w ∈ sphere (0:ℂ) R := by simpa [frontier_ball _ hR.ne'] using hw
    have H := ecanonical_log_norm_eq_on_sphere D hf hR hS hwS
    have HE := congrArg Real.exp H
    rw [Real.exp_log (norm_pos_iff.mpr (D.ne_zero w (sphere_subset_closedBall hwS))),
      Real.exp_log (norm_pos_iff.mpr (hS w hwS))] at HE
    exact HE ▸ hbound w hwS
  · simpa [closure_ball _ hR.ne'] using hz

end PrimeDegreePackets.AnalyticGrowth

open scoped Topology ComplexConjugate
namespace PrimeDegreePackets.AnalyticGrowth

lemma canonicalNumerator_norm_lower {R : ℝ} {ρ z : ℂ} (hR : 0 < R)
    (hρ : ‖ρ‖ ≤ R) (hz : ‖z‖ ≤ R/2) :
    R^2/2 ≤ ‖(R:ℂ)^2-conj ρ*z‖ := by
  have H := norm_sub_norm_le ((R:ℂ)^2) (conj ρ*z)
  simp only [norm_pow, norm_real, Real.norm_eq_abs, abs_of_pos hR,
    norm_mul, norm_conj] at H
  have H' := mul_le_mul hρ hz (norm_nonneg z) hR.le
  nlinarith

lemma canonicalNumerator_ne_zero {R : ℝ} {ρ z : ℂ} (hR : 0 < R)
    (hρ : ‖ρ‖ ≤ R) (hz : ‖z‖ ≤ R/2) : (R:ℂ)^2-conj ρ*z ≠ 0 := by
  exact norm_pos_iff.mp (lt_of_lt_of_le (by positivity) (canonicalNumerator_norm_lower hR hρ hz))

lemma norm_canonicalCorrection_sub_le {R : ℝ} {ρ z w : ℂ} (hR : 0 < R)
    (hρ : ‖ρ‖ ≤ R) (hz : ‖z‖ ≤ R/2) (hw : ‖w‖ ≤ R/2) :
    ‖canonicalCorrection R ρ z-canonicalCorrection R ρ w‖ ≤ 4/R^2*‖z-w‖ := by
  have hZ := canonicalNumerator_ne_zero hR hρ hz
  have hW := canonicalNumerator_ne_zero hR hρ hw
  have HE : canonicalCorrection R ρ z-canonicalCorrection R ρ w =
      (conj ρ)^2*(z-w)/(((R:ℂ)^2-conj ρ*z)*((R:ℂ)^2-conj ρ*w)) := by
    unfold canonicalCorrection
    field_simp
    ring
  rw [HE, norm_div, norm_mul, norm_mul, norm_pow, norm_conj]
  have Hden : R^4/4 ≤ ‖(R:ℂ)^2-conj ρ*z‖*‖(R:ℂ)^2-conj ρ*w‖ := by
    have H := mul_le_mul (canonicalNumerator_norm_lower hR hρ hz)
      (canonicalNumerator_norm_lower hR hρ hw) (by positivity : 0 ≤ R^2/2)
      (norm_nonneg _)
    nlinarith
  have Hn : ‖ρ‖^2*‖z-w‖ ≤ R^2*‖z-w‖ :=
    mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hρ 2) (norm_nonneg _)
  calc
    _ ≤ R^2*‖z-w‖/(R^4/4) := div_le_div₀ (by positivity) Hn (by positivity) Hden
    _ = _ := by field_simp

lemma logDeriv_canonicalFactor {R : ℝ} {ρ z : ℂ} (hR : R ≠ 0)
    (hz : z ≠ ρ) (hnum : (R:ℂ)^2-conj ρ*z ≠ 0) :
    logDeriv (canonicalFactor R ρ) z = -canonicalCorrection R ρ z - 1/(z-ρ) := by
  have HR : (R:ℂ) ≠ 0 := by exact_mod_cast hR
  have HZ : z-ρ ≠ 0 := sub_ne_zero.mpr hz
  have Hn : HasDerivAt (fun z : ℂ => (R:ℂ)^2-conj ρ*z) (-conj ρ) z := by
    apply ((hasDerivAt_const z ((R:ℂ)^2)).sub
      ((hasDerivAt_id z).const_mul (conj ρ))).congr_deriv
    simp
  have Hd : HasDerivAt (fun z : ℂ => (R:ℂ)*(z-ρ)) (R:ℂ) z := by
    apply (((hasDerivAt_id z).sub_const ρ).const_mul (R:ℂ)).congr_deriv
    simp
  unfold canonicalFactor
  rw [logDeriv_div (g := fun z : ℂ => (R:ℂ)*(z-ρ)) z hnum (mul_ne_zero HR HZ) Hn.differentiableAt Hd.differentiableAt]
  rw [logDeriv_apply, logDeriv_apply, Hn.deriv, Hd.deriv]
  unfold canonicalCorrection
  field_simp

end PrimeDegreePackets.AnalyticGrowth


namespace PrimeDegreePackets.AnalyticGrowth

 

lemma ecanonical_logDeriv {f g : ℂ → ℂ} {R : ℝ}
    (D : ECanonicalDecomp f g R) (hf : Differentiable ℂ f) (hR : 0 < R)
    (hS : ∀ z ∈ sphere (0:ℂ) R, f z ≠ 0) {z : ℂ}
    (hz : ‖z‖ ≤ R/2) (hfz : f z ≠ 0) :
    logDeriv f z = (∑ᶠ ρ, (divisor f (ball (0:ℂ) R) ρ : ℂ) *
      (1/(z-ρ)+canonicalCorrection R ρ z)) + logDeriv g z := by
  classical
  let t := D.meromorphicOn.divisor_ball_support_finite.toFinset
  have ht (ρ : ℂ) : ρ ∈ t ↔ divisor f (ball (0:ℂ) R) ρ ≠ 0 := by
    simp only [t, Set.Finite.mem_toFinset, Function.mem_support]
  have hρB (ρ : ℂ) (hρ : ρ ∈ t) : ρ ∈ ball (0:ℂ) R :=
    (divisor f (ball (0:ℂ) R)).supportWithinDomain ((ht ρ).mp hρ)
  have hzB : z ∈ closedBall (0:ℂ) R := mem_closedBall_zero_iff.mpr (by linarith)
  have havoid (ρ : ℂ) (hρ : ρ ∈ t) : z ≠ ρ := by
    intro H
    obtain rfl := H
    have HH := (ht z).mp hρ
    rw [MeromorphicOn.divisor_apply (fun z _ => (hf.analyticAt z).meromorphicAt) (hρB z hρ),
      (hf.analyticAt z).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr hfz] at HH
    simp at HH
  let P : ℂ → ℂ := fun x => ∏ ρ ∈ t, canonicalFactor R ρ x ^ (-divisor f (ball 0 R) ρ)
  have HPa : AnalyticAt ℂ P z := by
    apply Finset.analyticAt_fun_prod
    intro ρ hρ
    apply (analyticOnNhd_canonicalFactor R ρ z (havoid ρ hρ)).fun_zpow
    exact canonicalFactor_ne_zero (hρB ρ hρ) hzB (havoid ρ hρ)
  have HPz : P z ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro ρ hρ
    exact zpow_ne_zero _ (canonicalFactor_ne_zero (hρB ρ hρ) hzB (havoid ρ hρ))
  have HP : (∏ᶠ ρ, (canonicalFactor R ρ)^(-divisor f (ball (0:ℂ) R) ρ)) = P := by
    rw [finprod_eq_prod_of_mulSupport_subset (s := t) _ ?_]
    · ext x
      simp only [P, Finset.prod_apply, Pi.pow_apply]
    · intro ρ hρ
      apply (ht ρ).mpr
      intro H
      simp [H] at hρ
  have HE : f =ᶠ[codiscreteWithin (closedBall (0:ℂ) R)] (fun x => P x*g x) := by
    have H := D.eventuallyEq
    rw [HP, divisor_sphere_eq_zero hf hS] at H
    filter_upwards [H] with x hx
    simpa only [Function.locallyFinsuppWithin.coe_zero, Pi.zero_apply, zpow_zero,
      finprod_one, mul_one, Pi.smul_apply, smul_eq_mul, Pi.mul_apply] using hx
  have HEz : f =ᶠ[𝓝 z] (fun x => P x*g x) := by
    apply ((hf z).continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
      (HPa.mul (D.analyticOnNhd z hzB)).continuousAt).mp
    apply (hf.analyticAt z).meromorphicAt.eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin_preperfect
      (HPa.mul (D.analyticOnNhd z hzB)).meromorphicAt hzB _ HE
    rw [← closure_ball _ hR.ne']
    exact isOpen_ball.perfect_closure.2
  rw [(logDeriv_congr_nhds HEz).eq_of_nhds,
    logDeriv_mul z HPz (D.ne_zero z hzB) HPa.differentiableAt (D.analyticOnNhd z hzB).differentiableAt]
  congr 1
  change logDeriv (fun x => ∏ ρ ∈ t, canonicalFactor R ρ x ^ (-divisor f (ball 0 R) ρ)) z = _
  rw [logDeriv_prod (f := fun ρ x : ℂ => canonicalFactor R ρ x ^
    (-divisor f (ball 0 R) ρ)) (s := t) (x := z) (fun ρ hρ => zpow_ne_zero _
    (canonicalFactor_ne_zero (hρB ρ hρ) hzB (havoid ρ hρ))) (fun ρ hρ =>
      ((analyticOnNhd_canonicalFactor R ρ z (havoid ρ hρ)).fun_zpow
        (canonicalFactor_ne_zero (hρB ρ hρ) hzB (havoid ρ hρ))).differentiableAt)]
  rw [finsum_eq_sum_of_support_subset (s := t) _ (by
    intro ρ hρ
    apply (ht ρ).mpr
    intro H
    simp [H] at hρ)]
  apply Finset.sum_congr rfl
  intro ρ hρ
  rw [logDeriv_fun_zpow (analyticOnNhd_canonicalFactor R ρ z (havoid ρ hρ)).differentiableAt,
    logDeriv_canonicalFactor hR.ne' (havoid ρ hρ)
      (canonicalNumerator_ne_zero hR (mem_ball_zero_iff.mp (hρB ρ hρ)).le hz)]
  push_cast
  ring

end PrimeDegreePackets.AnalyticGrowth


namespace PrimeDegreePackets.AnalyticGrowth


lemma zeroMultiplicity_nonneg {f : ℂ → ℂ} (hf : Differentiable ℂ f) (z : ℂ) :
    0 ≤ zeroMultiplicity f z := by
  have H := AnalyticOnNhd.divisor_nonneg (fun z (_ : z ∈ (univ : Set ℂ)) => hf.analyticAt z) z
  simpa only [zeroMultiplicity, MeromorphicOn.divisor_apply
    (fun z _ => (hf.analyticAt z).meromorphicAt) (mem_univ z),
    Function.locallyFinsuppWithin.coe_zero, Pi.zero_apply] using H

lemma zeroMultiplicity_eq_zero_iff {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (h0 : f 0 ≠ 0) (z : ℂ) : zeroMultiplicity f z = 0 ↔ f z ≠ 0 := by
  rw [zeroMultiplicity, WithTop.untop₀_eq_zero]
  simp only [entire_order_ne_top hf h0 z, or_false,
    (hf.analyticAt z).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff]

lemma zeroMultiplicity_ne_zero_iff {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (h0 : f 0 ≠ 0) (z : ℂ) : zeroMultiplicity f z ≠ 0 ↔ f z = 0 := by
  simp [zeroMultiplicity_eq_zero_iff hf h0]

lemma exists_zero_free_sphere {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (h0 : f 0 ≠ 0) {a b : ℝ} (hab : a < b) :
    ∃ R ∈ Ioo a b, ∀ z ∈ sphere (0:ℂ) R, f z ≠ 0 := by
  have Hfin := ((divisor f (closedBall (0:ℂ) b)).finiteSupport (isCompact_closedBall 0 b)).image
    (fun z : ℂ => ‖z‖)
  obtain ⟨R,hR,H⟩ := (Set.Ioo_infinite hab).exists_notMem_finite Hfin
  refine ⟨R,hR,?_⟩
  intro z hz hz0
  apply H
  have HZ : ‖z‖ = R := mem_sphere_zero_iff_norm.mp hz
  refine ⟨z,?_,HZ⟩
  change divisor f (closedBall (0:ℂ) b) z ≠ 0
  rw [MeromorphicOn.divisor_apply (fun z _ => (hf.analyticAt z).meromorphicAt)
    (show z ∈ closedBall (0:ℂ) b from mem_closedBall_zero_iff.mpr (HZ ▸ hR.2.le))]
  exact (zeroMultiplicity_ne_zero_iff hf h0 z).mpr hz0


lemma diskZeroCount_eq_finsum (f : ℂ → ℂ) (R : ℝ) :
    diskZeroCount f R = ∑ᶠ z, (divisor f (closedBall (0:ℂ) R) z : ℝ) := by
  exact map_finsum (Int.castRingHom ℝ)
    ((divisor f (closedBall (0:ℂ) R)).finiteSupport (isCompact_closedBall 0 R))


lemma diskZeroCount_le {f : ℂ → ℂ} (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0)
    {R B : ℝ} (hR : 0 < R) (hB : 0 ≤ B)
    (hbound : ∀ z : ℂ, ‖z‖ ≤ 2*R → ‖f z‖ ≤ Real.exp B) :
    diskZeroCount f R ≤ (B-Real.log ‖f 0‖)/Real.log 2 := by
  have H := AnalyticOnNhd.sum_divisor_le (f := f) (c := (0:ℂ)) (r := R) (R := 2*R)
    (by simpa [abs_of_pos hR] using hR)
    (by rw [abs_of_pos hR, abs_of_pos (by positivity : 0 < 2*R)]; linarith)
    (Real.one_le_exp_iff.mpr hB) (fun z _ => hf.analyticAt z) h0
    (fun z hz => hbound z (by
      simpa only [abs_of_pos (by positivity : 0 < 2*R)] using
        le_of_eq (mem_sphere_zero_iff_norm.mp hz)))
  rw [abs_of_pos hR] at H
  have HE : 2*R/R = 2 := by field_simp
  simpa only [diskZeroCount, abs_of_pos hR, Real.log_div (Real.exp_ne_zero B)
    (norm_ne_zero_iff.mpr h0), Real.log_exp, HE] using H

end PrimeDegreePackets.AnalyticGrowth
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_MellinGrowth
attribute [-instance] _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space
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


namespace PrimeDegreePackets.AnalyticGrowth

 

lemma diskZeroCount_subquadratic {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (h0 : f 0 ≠ 0) (hg : HasSubquadraticGrowth f) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ R : ℝ in atTop, diskZeroCount f R ≤ ε*R^2 := by
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have HT : Tendsto (fun R : ℝ => 2*R) atTop atTop :=
    Tendsto.const_mul_atTop (by norm_num : (0:ℝ) < 2) tendsto_id
  have HB := HT.eventually (hg (ε*Real.log 2/8) (by positivity))
  have HC := (tendsto_const_mul_pow_atTop (by decide : (2:ℕ) ≠ 0)
    (by positivity : 0 < ε*Real.log 2/2)).eventually_ge_atTop (-Real.log ‖f 0‖)
  filter_upwards [HB, HC, eventually_gt_atTop (0:ℝ)] with R hB hC hR
  apply (diskZeroCount_le hf h0 hR (by positivity) hB).trans
  apply (div_le_iff₀ hL).mpr
  nlinarith

end PrimeDegreePackets.AnalyticGrowth


namespace PrimeDegreePackets.AnalyticGrowth

lemma divisor_ball_eq_closedBall {f : ℂ → ℂ} {R : ℝ} (hf : Differentiable ℂ f)
    (hS : ∀ z ∈ sphere (0:ℂ) R, f z ≠ 0) :
    (divisor f (ball (0:ℂ) R) : ℂ → ℤ) = divisor f (closedBall (0:ℂ) R) := by
  ext z
  by_cases hz : z ∈ ball (0:ℂ) R
  · rw [MeromorphicOn.divisor_apply (fun z _ => (hf.analyticAt z).meromorphicAt) hz,
      MeromorphicOn.divisor_apply (fun z _ => (hf.analyticAt z).meromorphicAt)
        (ball_subset_closedBall hz)]
  · by_cases hzC : z ∈ closedBall (0:ℂ) R
    · have hzS : z ∈ sphere (0:ℂ) R := by
        rw [mem_sphere_zero_iff_norm]
        exact le_antisymm (mem_closedBall_zero_iff.mp hzC) (not_lt.mp (by simpa using hz))
      rw [MeromorphicOn.divisor_apply (fun z _ => (hf.analyticAt z).meromorphicAt) hzC,
        (hf.analyticAt z).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr (hS z hzS)]
      simp [hz]
    · simp [hz, hzC]

lemma mem_zeroDiskFinset (f : ℂ → ℂ) (R : ℝ) (z : ℂ) :
    z ∈ zeroDiskFinset f R ↔ divisor f (closedBall (0:ℂ) R) z ≠ 0 := by
  simp [zeroDiskFinset, Function.mem_support]

lemma zeroDiskFinset_norm_le {f : ℂ → ℂ} {R : ℝ} {z : ℂ}
    (hz : z ∈ zeroDiskFinset f R) : ‖z‖ ≤ R :=
  mem_closedBall_zero_iff.mp ((divisor f (closedBall (0:ℂ) R)).supportWithinDomain
    ((mem_zeroDiskFinset f R z).mp hz))

lemma divisor_closedBall_eq_multiplicity {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {R : ℝ} {z : ℂ} (hz : ‖z‖ ≤ R) :
    divisor f (closedBall (0:ℂ) R) z = zeroMultiplicity f z :=
  MeromorphicOn.divisor_apply (fun z _ => (hf.analyticAt z).meromorphicAt)
    (mem_closedBall_zero_iff.mpr hz)

lemma diskZeroCount_eq_sum {f : ℂ → ℂ} (hf : Differentiable ℂ f) (R : ℝ) :
    diskZeroCount f R = ∑ ρ ∈ zeroDiskFinset f R, (zeroMultiplicity f ρ : ℝ) := by
  classical
  rw [diskZeroCount_eq_finsum, finsum_eq_sum_of_support_subset (s := zeroDiskFinset f R) _ (by
    intro z hz
    apply (mem_zeroDiskFinset f R z).mpr
    intro H
    simp [H] at hz)]
  apply Finset.sum_congr rfl
  intro ρ hρ
  rw [divisor_closedBall_eq_multiplicity hf (zeroDiskFinset_norm_le hρ)]

lemma ecanonical_logDeriv_finite {f g : ℂ → ℂ} {R : ℝ}
    (D : ECanonicalDecomp f g R) (hf : Differentiable ℂ f) (hR : 0 < R)
    (hS : ∀ z ∈ sphere (0:ℂ) R, f z ≠ 0) {z : ℂ}
    (hz : ‖z‖ ≤ R/2) (hfz : f z ≠ 0) :
    logDeriv f z = diskPoleSum f R z +
      (∑ ρ ∈ zeroDiskFinset f R, (zeroMultiplicity f ρ : ℂ)*canonicalCorrection R ρ z) +
      logDeriv g z := by
  classical
  rw [ecanonical_logDeriv D hf hR hS hz hfz, divisor_ball_eq_closedBall hf hS]
  rw [finsum_eq_sum_of_support_subset (s := zeroDiskFinset f R) _ (by
    intro ρ hρ
    apply (mem_zeroDiskFinset f R ρ).mpr
    intro H
    simp [H] at hρ)]
  congr 1
  simp only [diskPoleSum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ρ hρ
  rw [divisor_closedBall_eq_multiplicity hf (zeroDiskFinset_norm_le hρ), mul_add]

lemma correction_sum_sub_le {f : ℂ → ℂ} (hf : Differentiable ℂ f) {R : ℝ}
    (hR : 0 < R) {z w : ℂ} (hz : ‖z‖ ≤ R/2) (hw : ‖w‖ ≤ R/2) :
    ‖(∑ ρ ∈ zeroDiskFinset f R, (zeroMultiplicity f ρ : ℂ)*canonicalCorrection R ρ z) -
      (∑ ρ ∈ zeroDiskFinset f R, (zeroMultiplicity f ρ : ℂ)*canonicalCorrection R ρ w)‖ ≤
      (4*diskZeroCount f R/R^2)*‖z-w‖ := by
  classical
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ ρ ∈ zeroDiskFinset f R, ‖(zeroMultiplicity f ρ : ℂ)*
        canonicalCorrection R ρ z-(zeroMultiplicity f ρ : ℂ)*canonicalCorrection R ρ w‖ :=
      norm_sum_le _ _
    _ ≤ ∑ ρ ∈ zeroDiskFinset f R, (zeroMultiplicity f ρ : ℝ)*(4/R^2*‖z-w‖) := by
      apply Finset.sum_le_sum
      intro ρ hρ
      rw [← mul_sub, norm_mul, Complex.norm_intCast,
        abs_of_nonneg (show (0:ℝ) ≤ zeroMultiplicity f ρ by exact_mod_cast zeroMultiplicity_nonneg hf ρ)]
      exact mul_le_mul_of_nonneg_left
        (norm_canonicalCorrection_sub_le hR (zeroDiskFinset_norm_le hρ) hz hw)
        (by exact_mod_cast zeroMultiplicity_nonneg hf ρ)
    _ = _ := by rw [← Finset.sum_mul, ← diskZeroCount_eq_sum hf]; ring

lemma diskPoleSum_error_le {f : ℂ → ℂ} (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0)
    {R B : ℝ} (hR : 0 < R) (hS : ∀ z ∈ sphere (0:ℂ) R, f z ≠ 0)
    (hbound : ∀ z ∈ sphere (0:ℂ) R, ‖f z‖ ≤ Real.exp B)
    (hB : Real.log ‖f 0‖ < B) {z w : ℂ}
    (hz : ‖z‖ < R/4) (hw : ‖w‖ < R/4) (hfz : f z ≠ 0) (hfw : f w ≠ 0) :
    ‖(logDeriv f z-logDeriv f w)-(diskPoleSum f R z-diskPoleSum f R w)‖ ≤
      ((64*(B-Real.log ‖f 0‖)+4*diskZeroCount f R)/R^2)*‖z-w‖ := by
  obtain ⟨g,D⟩ := exists_entire_ecanonicalDecomp (R := R) hf h0
  have hz' : ‖z‖ ≤ R/2 := by linarith
  have hw' : ‖w‖ ≤ R/2 := by linarith
  have HE : (logDeriv f z-logDeriv f w)-(diskPoleSum f R z-diskPoleSum f R w) =
      ((∑ ρ ∈ zeroDiskFinset f R, (zeroMultiplicity f ρ : ℂ)*canonicalCorrection R ρ z) -
       (∑ ρ ∈ zeroDiskFinset f R, (zeroMultiplicity f ρ : ℂ)*canonicalCorrection R ρ w)) +
      (logDeriv g z-logDeriv g w) := by
    rw [ecanonical_logDeriv_finite D hf hR hS hz' hfz,
      ecanonical_logDeriv_finite D hf hR hS hw' hfw]
    ring
  rw [HE]
  apply (norm_add_le _ _).trans
  have Hg := logDeriv_sub_le_of_log_norm_le hR (sub_pos.mpr hB)
    (D.analyticOnNhd.differentiableOn.mono ball_subset_closedBall)
    (fun z hz => D.ne_zero z (ball_subset_closedBall hz))
    (fun z hz => sub_le_sub (ecanonical_log_norm_le D hf hR hS hbound (ball_subset_closedBall hz))
      (ecanonical_log_norm_zero_ge D hf hR hS h0))
    (mem_ball_zero_iff.mpr hz) (mem_ball_zero_iff.mpr hw)
  have HC := correction_sum_sub_le hf hR hz' hw'
  calc
    _ ≤ (4*diskZeroCount f R/R^2)*‖z-w‖ +
      (64*(B-Real.log ‖f 0‖)/R^2)*‖z-w‖ := add_le_add HC Hg
    _ = _ := by ring

end PrimeDegreePackets.AnalyticGrowth


namespace PrimeDegreePackets.AnalyticGrowth

 

lemma tendsto_diskPoleSum_sub {f : ℂ → ℂ} (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0)
    (hg : HasSubquadraticGrowth f) {ι : Type*} {l : Filter ι} {r : ι → ℝ}
    (hr : Tendsto r l atTop) (hS : ∀ᶠ i in l, ∀ z ∈ sphere (0:ℂ) (r i), f z ≠ 0)
    {z w : ℂ} (hfz : f z ≠ 0) (hfw : f w ≠ 0) :
    Tendsto (fun i => diskPoleSum f (r i) z-diskPoleSum f (r i) w) l
      (𝓝 (logDeriv f z-logDeriv f w)) := by
  apply Metric.tendsto_nhds.2
  intro ε hε
  let η := ε/(200*(‖z-w‖+1))
  have hη : 0 < η := by dsimp [η] <;> positivity
  have HP := (tendsto_const_mul_pow_atTop (by decide : (2:ℕ) ≠ 0) hη).eventually_ge_atTop
    (|Real.log ‖f 0‖|+1-Real.log ‖f 0‖)
  filter_upwards [hr.eventually (hg η hη), hr.eventually (diskZeroCount_subquadratic hf h0 hg hη),
    hr.eventually HP, hr.eventually (eventually_gt_atTop (4*(‖z‖+‖w‖+1))), hS]
    with i hG hN hP hR hS'
  have hR0 : 0 < r i := by linarith [norm_nonneg z, norm_nonneg w]
  have hz : ‖z‖ < r i/4 := by linarith [norm_nonneg w]
  have hw : ‖w‖ < r i/4 := by linarith [norm_nonneg z]
  have HB : Real.log ‖f 0‖ < η*(r i)^2+|Real.log ‖f 0‖|+1 := by
    nlinarith [le_abs_self (Real.log ‖f 0‖), sq_nonneg (r i)]
  have H := diskPoleSum_error_le hf h0 hR0 hS' (B := η*(r i)^2+|Real.log ‖f 0‖|+1)
    (fun a ha => (hG a (le_of_eq (mem_sphere_zero_iff_norm.mp ha))).trans
      (Real.exp_le_exp.mpr (by linarith [abs_nonneg (Real.log ‖f 0‖)]))) HB hz hw hfz hfw
  rw [dist_eq_norm']
  apply H.trans_lt
  have HE : (64*(η*(r i)^2+|Real.log ‖f 0‖|+1-Real.log ‖f 0‖)+4*diskZeroCount f (r i))/(r i)^2
      ≤ 132*η := by
    apply (div_le_iff₀ (sq_pos_of_pos hR0)).mpr
    nlinarith
  calc
    _ ≤ (132*η)*‖z-w‖ := mul_le_mul_of_nonneg_right HE (norm_nonneg _)
    _ < ε := by
      dsimp [η]
      have Hden : 0 < 200*(‖z-w‖+1) := by positivity
      rw [show 132*(ε/(200*(‖z-w‖+1)))*‖z-w‖ =
        ε*(132*‖z-w‖)/(200*(‖z-w‖+1)) by ring]
      apply (div_lt_iff₀ Hden).mpr
      nlinarith [norm_nonneg (z-w)]

 

lemma exists_good_radii {f : ℂ → ℂ} (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0) :
    ∃ r : ℕ → ℝ, Tendsto r atTop atTop ∧
      (∀ j : ℕ, (j:ℝ)+1 < r j ∧ r j < j+2) ∧
      ∀ j z, z ∈ sphere (0:ℂ) (r j) → f z ≠ 0 := by
  choose r hR hS using fun j : ℕ => exists_zero_free_sphere hf h0
    (show (j:ℝ)+1 < j+2 by linarith)
  refine ⟨r,?_,hR,hS⟩
  apply tendsto_atTop_mono (fun j => (hR j).1.le)
  exact tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop

end PrimeDegreePackets.AnalyticGrowth
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_ZeroReflection
attribute [-instance] _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.finiteIdeleGroupT2Space _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue
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
namespace PrimeDegreePackets.AnalyticGrowth

lemma zeroMultiplicity_reflection {f : ℂ → ℂ} (hfe : ∀ z, f (1-z) = f z) (z : ℂ) :
    zeroMultiplicity f (1-z) = zeroMultiplicity f z := by
  have Hg : HasDerivAt (fun z : ℂ => 1-z) (-1) z := by
    apply ((hasDerivAt_id z).const_sub 1).congr_deriv
    simp
  have H := meromorphicOrderAt_comp_of_deriv_ne_zero (f := f)
    (g := fun z : ℂ => 1-z) (x := z) (analyticAt_const.sub analyticAt_id) (by rw [Hg.deriv]; norm_num)
  have HE : f ∘ (fun z : ℂ => 1-z) = f := funext hfe
  rw [HE] at H
  exact congrArg WithTop.untop₀ H.symm

lemma logDeriv_reflection {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hfe : ∀ z, f (1-z) = f z) (z : ℂ) : logDeriv f (1-z) = -logDeriv f z := by
  have Hg : HasDerivAt (fun z : ℂ => 1-z) (-1) z := by
    apply ((hasDerivAt_id z).const_sub 1).congr_deriv
    simp
  have H := ((hf (1-z)).hasDerivAt.comp z Hg)
  have HE : (fun z : ℂ => f (1-z)) = f := funext hfe
  simp only [Function.comp_def] at H
  rw [HE] at H
  have HD := H.deriv
  rw [logDeriv_apply, logDeriv_apply, hfe]
  have HD' : deriv f (1-z) = -deriv f z := by linear_combination HD
  rw [HD', neg_div]

 

lemma hasSum_of_nonneg_finite_exhaustion {α ι : Type*} {l : Filter ι} [NeBot l]
    {a : α → ℝ} (ha : ∀ x, 0 ≤ a x) (t : ι → Finset α)
    (ht : ∀ x, a x ≠ 0 → ∀ᶠ i in l, x ∈ t i) {A : ℝ}
    (hA : Tendsto (fun i => ∑ x ∈ t i, a x) l (𝓝 A)) : HasSum a A := by
  classical
  have HB : ∀ s : Finset α, ∑ x ∈ s, a x ≤ A := by
    intro s
    have H : ∀ᶠ i in l, ∀ x ∈ s, a x ≠ 0 → x ∈ t i := by
      rw [Filter.eventually_all_finset]
      intro x hx
      by_cases hx0 : a x = 0
      · exact Filter.Eventually.of_forall (by simp [hx0])
      · exact (ht x hx0).mono (fun i hi _ => hi)
    apply ge_of_tendsto hA
    filter_upwards [H] with i hi
    calc
      _ = ∑ x ∈ s.filter (fun x => a x ≠ 0), a x := by
        symm
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro x hx hn
        by_contra h
        exact hn (Finset.mem_filter.mpr ⟨hx,h⟩)
      _ ≤ ∑ x ∈ t i, a x := Finset.sum_le_sum_of_subset_of_nonneg
        (fun x hx => hi x (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hx).2)
        (fun x _ _ => ha x)
  have HS := summable_of_sum_le ha HB
  have HE : ∑' x, a x = A := le_antisymm (HS.tsum_le_of_sum_le HB)
    (le_of_tendsto hA (Filter.Eventually.of_forall (fun i => HS.sum_le_tsum (t i) (fun x _ => ha x))))
  exact HE ▸ HS.hasSum

end PrimeDegreePackets.AnalyticGrowth


namespace PrimeDegreePackets.AnalyticGrowth


lemma realZeroPole_nonneg {f : ℂ → ℂ} (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0)
    (hstrip : ∀ ρ, f ρ = 0 → ρ.re ≤ 1) {σ : ℝ} (hσ : 1 < σ) (ρ : ℂ) :
    0 ≤ realZeroPole f σ ρ := by
  by_cases hm : zeroMultiplicity f ρ = 0
  · simp [realZeroPole, hm]
  have hρ := hstrip ρ ((zeroMultiplicity_ne_zero_iff hf h0 ρ).mp hm)
  unfold realZeroPole
  apply mul_nonneg (by exact_mod_cast zeroMultiplicity_nonneg hf ρ)
  simp only [one_div, Complex.inv_re, Complex.sub_re, Complex.ofReal_re]
  exact div_nonneg (by linarith) (Complex.normSq_nonneg _)

lemma realZeroPole_pair {f : ℂ → ℂ} (hfe : ∀ z, f (1-z) = f z)
    (σ : ℝ) (ρ : ℂ) :
    realZeroPole f σ ρ + realZeroPole f σ (1-ρ) =
      ((zeroMultiplicity f ρ : ℂ)*(1/((σ:ℂ)-ρ)-1/((1-(σ:ℂ))-ρ))).re := by
  have HE : (σ:ℂ)-(1-ρ) = -((1-(σ:ℂ))-ρ) := by ring
  simp only [realZeroPole, zeroMultiplicity_reflection hfe, HE, one_div, inv_neg,
    Complex.neg_re, Complex.mul_re, Complex.intCast_re, Complex.intCast_im,
    zero_mul, sub_zero, Complex.sub_re]
  ring

lemma diskPoleSum_sub_re {f : ℂ → ℂ} (hfe : ∀ z, f (1-z) = f z)
    (σ R : ℝ) :
    (diskPoleSum f R σ-diskPoleSum f R (1-(σ:ℂ))).re =
      ∑ ρ ∈ zeroDiskFinset f R, (realZeroPole f σ ρ+realZeroPole f σ (1-ρ)) := by
  classical
  simp only [diskPoleSum, ← Finset.sum_sub_distrib, ← mul_sub,
    realZeroPole_pair hfe]
  exact map_sum Complex.reAddGroupHom _ _

 

theorem hasSum_realZeroPole {f : ℂ → ℂ} (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0)
    (hg : HasSubquadraticGrowth f) (hfe : ∀ z, f (1-z) = f z)
    (hstrip : ∀ ρ, f ρ = 0 → ρ.re ≤ 1) {σ : ℝ} (hσ : 1 < σ) :
    HasSum (realZeroPole f σ) (logDeriv f σ).re := by
  classical
  have hσ0 : f (σ:ℂ) ≠ 0 := by
    intro h
    have HH := hstrip σ h
    simp only [Complex.ofReal_re] at HH
    linarith
  have hσ1 : f (1-(σ:ℂ)) ≠ 0 := by rwa [hfe]
  obtain ⟨r,hr,_,hS⟩ := exists_good_radii hf h0
  have HT := (Complex.continuous_re.tendsto _).comp (tendsto_diskPoleSum_sub hf h0 hg hr
    (Filter.Eventually.of_forall hS) hσ0 hσ1)
  have HT' : Tendsto (fun j => ∑ ρ ∈ zeroDiskFinset f (r j),
      (realZeroPole f σ ρ+realZeroPole f σ (1-ρ))) atTop (𝓝 (2*(logDeriv f σ).re)) := by
    simpa only [Function.comp_def, diskPoleSum_sub_re hfe,
      logDeriv_reflection hf hfe, Complex.sub_re, Complex.neg_re, sub_neg_eq_add, two_mul, Complex.add_re] using HT
  have HNN := realZeroPole_nonneg hf h0 hstrip hσ
  have Hsum : HasSum (fun ρ => realZeroPole f σ ρ+realZeroPole f σ (1-ρ))
      (2*(logDeriv f σ).re) := by
    apply hasSum_of_nonneg_finite_exhaustion (fun ρ => add_nonneg (HNN ρ) (HNN (1-ρ)))
      (fun j => zeroDiskFinset f (r j)) _ HT'
    intro ρ hρ
    have Hm : zeroMultiplicity f ρ ≠ 0 := by
      intro H
      apply hρ
      simp [realZeroPole, zeroMultiplicity_reflection hfe, H]
    filter_upwards [hr.eventually_ge_atTop ‖ρ‖] with j hj
    rw [mem_zeroDiskFinset, divisor_closedBall_eq_multiplicity hf hj]
    exact Hm
  have HS : Summable (realZeroPole f σ) := Hsum.summable.of_nonneg_of_le HNN
    (fun ρ => le_add_of_nonneg_right (HNN (1-ρ)))
  let e : ℂ ≃ ℂ := ⟨fun ρ => 1-ρ, fun ρ => 1-ρ, by intro ρ; ring, by intro ρ; ring⟩
  have HS' : Summable (fun ρ => realZeroPole f σ (1-ρ)) := e.summable_iff.mpr HS
  have HE : (∑' ρ, realZeroPole f σ (1-ρ)) = ∑' ρ, realZeroPole f σ ρ :=
    e.tsum_eq (realZeroPole f σ)
  have HH := Hsum.tsum_eq
  rw [HS.tsum_add HS', HE] at HH
  have HA : (∑' ρ, realZeroPole f σ ρ) = (logDeriv f σ).re := by linarith
  exact HA ▸ HS.hasSum

end PrimeDegreePackets.AnalyticGrowth


end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_SubquadraticGrowth
attribute [-instance] _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.finiteIdeleGroupT2Space _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue
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
namespace PrimeDegreePackets.AnalyticGrowth

lemma near_one_kernel_lower {a b : ℝ} (ha : 1 ≤ a) (ha' : a ≤ 5/4)
    (hb : |b| ≤ 1/4) : (10/13:ℝ) ≤ a/(a^2+b^2) := by
  have hb' := abs_le.mp hb
  have hbs : b^2 ≤ 1/16 := by nlinarith
  have hd : 0 < a^2+b^2 := by nlinarith [sq_nonneg b]
  apply (le_div_iff₀ hd).mpr
  have Hp : 0 ≤ (5/4-a)*(10*a-1/2) := mul_nonneg (by linarith) (by linarith)
  nlinarith

lemma real_inverse_pole_scaled {L h : ℝ} (hL : L ≠ 0) (ρ : ℂ) :
    (1/(((1+h:ℝ):ℂ)-ρ)).re =
      L*((L*(1-ρ.re)+L*h)/((L*(1-ρ.re)+L*h)^2+(L*ρ.im)^2)) := by
  simp only [one_div, Complex.inv_re, Complex.sub_re, Complex.ofReal_re,
    Complex.normSq_apply, Complex.sub_im, Complex.ofReal_im, zero_sub]
  have HE : L*(1-ρ.re)+L*h = L*(1+h-ρ.re) := by ring
  rw [HE]
  simp only [mul_pow, neg_mul_neg]
  rw [← mul_add, ← mul_div_assoc, ← mul_assoc, ← pow_two]
  rw [show L*L = L^2 by ring]
  rw [mul_div_mul_left _ _ (pow_ne_zero 2 hL)]
  congr 1; ring

 

lemma near_one_complex_pole_lower {L : ℝ} (hL : 0 < L) {ρ : ℂ}
    (hβ : ρ.re ≤ 1) (hβ' : 1-1/(4*L) ≤ ρ.re) (hγ : |ρ.im| ≤ 1/(4*L)) :
    (10/13)*L ≤ (1/(((1+1/L:ℝ):ℂ)-ρ)).re := by
  have hX : 0 ≤ L*(1-ρ.re) := mul_nonneg hL.le (by linarith)
  have hX' : L*(1-ρ.re) ≤ 1/4 := by
    have H := mul_le_mul_of_nonneg_left (show 1-ρ.re ≤ 1/(4*L) by linarith) hL.le
    have HE : L*(1/(4*L)) = (1/4:ℝ) := by field_simp
    rwa [HE] at H
  have hY : |L*ρ.im| ≤ 1/4 := by
    rw [abs_mul, abs_of_pos hL]
    have H := mul_le_mul_of_nonneg_left hγ hL.le
    have HE : L*(1/(4*L)) = (1/4:ℝ) := by field_simp
    rwa [HE] at H
  have H := near_one_kernel_lower (a := L*(1-ρ.re)+1) (by linarith) (by linarith) hY
  rw [real_inverse_pole_scaled hL.ne', mul_one_div_cancel hL.ne']
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left H hL.le

end PrimeDegreePackets.AnalyticGrowth

open Complex Set Filter
namespace PrimeDegreePackets.AnalyticGrowth



lemma nearOneBox_multiplicity_sum_le_one {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0) (hg : HasSubquadraticGrowth f)
    (hfe : ∀ z, f (1-z) = f z) (hstrip : ∀ ρ, f ρ = 0 → ρ.re ≤ 1)
    {L A : ℝ} (hL : 0 < L) (hA : 26*A < L)
    (hbound : (logDeriv f (((1+1/L:ℝ)):ℂ)).re ≤ (3/2)*L+A)
    (t : Finset ℂ) (ht : ∀ ρ ∈ t, f ρ = 0 ∧ InNearOneBox L ρ) :
    ∑ ρ ∈ t, zeroMultiplicity f ρ ≤ 1 := by
  have hs : 1 < 1+1/L := by have H := one_div_pos.mpr hL; linarith
  have HS := hasSum_realZeroPole hf h0 hg hfe hstrip hs
  have Hlower : (10/13)*L*(∑ ρ ∈ t, (zeroMultiplicity f ρ : ℝ)) ≤
      ∑ ρ ∈ t, realZeroPole f (1+1/L) ρ := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro ρ hρ
    have H := near_one_complex_pole_lower hL (hstrip ρ (ht ρ hρ).1)
      (ht ρ hρ).2.1 (ht ρ hρ).2.2
    simpa only [realZeroPole, mul_comm] using mul_le_mul_of_nonneg_left H
      (show (0:ℝ) ≤ zeroMultiplicity f ρ by exact_mod_cast zeroMultiplicity_nonneg hf ρ)
  have Hupper := (HS.summable.sum_le_tsum t
    (fun ρ _ => realZeroPole_nonneg hf h0 hstrip hs ρ)).trans_eq HS.tsum_eq
  have Htotal := Hlower.trans (Hupper.trans hbound)
  by_contra h
  have Htwo : (2:ℤ) ≤ ∑ ρ ∈ t, zeroMultiplicity f ρ := by omega
  have Htwo' : (2:ℝ) ≤ ∑ ρ ∈ t, (zeroMultiplicity f ρ : ℝ) := by exact_mod_cast Htwo
  have HH := mul_le_mul_of_nonneg_left Htwo' (show 0 ≤ (10/13)*L by positivity)
  nlinarith

 

theorem nearOneBox_real_simple_unique {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0) (hg : HasSubquadraticGrowth f)
    (hfe : ∀ z, f (1-z) = f z) (hconj : ∀ z, f (conj z) = conj (f z))
    (hstrip : ∀ ρ, f ρ = 0 → ρ.re ≤ 1)
    {L A : ℝ} (hL : 0 < L) (hA : 26*A < L)
    (hbound : (logDeriv f (((1+1/L:ℝ)):ℂ)).re ≤ (3/2)*L+A)
    {ρ : ℂ} (hρ : f ρ = 0) (hbox : InNearOneBox L ρ) :
    zeroMultiplicity f ρ = 1 ∧ ρ.im = 0 ∧
      ∀ τ, f τ = 0 → InNearOneBox L τ → τ = ρ := by
  classical
  have HP {τ : ℂ} (hτ : f τ = 0) : 1 ≤ zeroMultiplicity f τ := by
    have H := zeroMultiplicity_nonneg hf τ
    have H' := (zeroMultiplicity_ne_zero_iff hf h0 τ).mpr hτ
    omega
  have Huniq : ∀ τ, f τ = 0 → InNearOneBox L τ → τ = ρ := by
    intro τ hτ hτbox
    by_contra hne
    have H := nearOneBox_multiplicity_sum_le_one hf h0 hg hfe hstrip hL hA hbound
      {τ,ρ} (by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact ⟨hτ,hτbox⟩
        · exact ⟨hρ,hbox⟩)
    simp only [Finset.sum_pair hne] at H
    have Hτ := HP hτ
    have Hρ := HP hρ
    omega
  have Hsimple := nearOneBox_multiplicity_sum_le_one hf h0 hg hfe hstrip hL hA hbound
    {ρ} (by intro z hz; have H := Finset.mem_singleton.mp hz; subst z; exact ⟨hρ,hbox⟩)
  have HS : zeroMultiplicity f ρ = 1 := by
    simp only [Finset.sum_singleton] at Hsimple
    exact le_antisymm Hsimple (HP hρ)
  have Hc := Huniq (conj ρ) (by rw [hconj, hρ]; simp) (by
    simpa only [InNearOneBox, Complex.conj_re, Complex.conj_im, abs_neg] using hbox)
  have HI := congrArg Complex.im Hc
  simp only [Complex.conj_im] at HI
  exact ⟨HS, by linarith, Huniq⟩

end PrimeDegreePackets.AnalyticGrowth

open scoped Topology NumberField ComplexConjugate
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_FunctionalEquation
attribute [-instance] _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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

lemma completedThetaXi_ne_zero_of_re_gt_one_totallyReal {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1)  {s : ℂ} (hs : 1 < s.re) :
    completedThetaXi σ hn s ≠ 0 := by
  rw [completedThetaXi_eq_totallyReal σ hn  hs]
  exact totallyRealCompletedXi_ne_zero K hs

lemma completedThetaXi_ne_zero_of_re_neg_totallyReal {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1)  {s : ℂ} (hs : s.re < 0) :
    completedThetaXi σ hn s ≠ 0 := by
  rw [completedThetaXi_functionalEquation_totallyReal σ hn  s]
  apply completedThetaXi_ne_zero_of_re_gt_one_totallyReal σ hn 
  simp only [Complex.sub_re, Complex.one_re]
  linarith

lemma dedekindXiZeros_re_mem_Icc_totallyReal {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1) 
    {s : ℂ} (hs : s ∈ dedekindXiZeros σ hn) : s.re ∈ Icc (0:ℝ) 1 := by
  constructor
  · by_contra h
    exact completedThetaXi_ne_zero_of_re_neg_totallyReal σ hn  (lt_of_not_ge h) hs
  · by_contra h
    exact completedThetaXi_ne_zero_of_re_gt_one_totallyReal σ hn  (lt_of_not_ge h) hs

end PrimeDegreePackets.HeckeMellin


namespace PrimeDegreePackets.HeckeMellin
open AnalyticGrowth

theorem dedekind_near_one_zero_real_simple_unique_totallyReal (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K],
      ∀ (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
        ,
      C < Real.log |(NumberField.discr K : ℝ)| →
      ∀ ρ, ρ ∈ dedekindXiZeros σ hn →
        InNearOneBox (Real.log |(NumberField.discr K : ℝ)|) ρ →
        zeroMultiplicity (completedThetaXi σ hn) ρ = 1 ∧ ρ.im = 0 ∧
          ∀ τ, τ ∈ dedekindXiZeros σ hn →
            InNearOneBox (Real.log |(NumberField.discr K : ℝ)|) τ → τ = ρ := by
  obtain ⟨B,hB,harch⟩ := archimedeanZetaTerm_bounded (d+1)
  refine ⟨max 1 (26*(B+1)), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro K _ _ _ σ hn  hL ρ hρ hρbox
  have hL1 : 1 < Real.log |(NumberField.discr K : ℝ)| :=
    lt_of_le_of_lt (le_max_left _ _) hL
  have hLp : 0 < Real.log |(NumberField.discr K : ℝ)| := by linarith
  have Hbase := completedThetaXi_logDeriv_base_le_totallyReal σ hn  rfl hL1.le harch
  apply nearOneBox_real_simple_unique (completedThetaXi_entire σ hn)
    (dedekindXiZeros_ne_zero_totallyReal σ hn ) (completedThetaXi_hasSubquadraticGrowth σ hn)
    (fun z => (completedThetaXi_functionalEquation_totallyReal σ hn  z).symm)
    (completedThetaXi_conj_totallyReal σ hn )
    (fun z hz => (dedekindXiZeros_re_mem_Icc_totallyReal σ hn  hz).2)
    hLp (lt_of_le_of_lt (le_max_right _ _) hL) _ hρ hρbox
  simpa only [add_assoc] using Hbase

end PrimeDegreePackets.HeckeMellin

open IntermediateField Module

open Module IntermediateField
open scoped BigOperators NumberField Pointwise
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Arithmetic_StarkZeros
attribute [-instance] _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue
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

/-- Uniqueness of a near-one zero reduces complex zero separation to
real-zero exclusion. -/
theorem completedXiGap_of_exceptionalRealZeroExclusion_oai (d : ℕ)
    (H : ExceptionalRealZeroExclusion.{u} d) : CompletedXiGap.{u} d := by
  obtain ⟨a, L₀, ha, hL₀, Hex⟩ := H
  obtain ⟨C, _, Hunique⟩ := dedekind_near_one_zero_real_simple_unique_totallyReal d
  let c : ℝ := min a (1 / 4)
  have hc : 0 < c := lt_min ha (by norm_num)
  refine ⟨c, max L₀ C + 1, hc, by have := le_max_left L₀ C; linarith, ?_⟩
  intro K _ _ _ hn σ hL z hz
  let L := Real.log |(NumberField.discr K : ℝ)|
  have hLC : C < L := by have := le_max_right L₀ C; dsimp [L] <;> linarith
  have hLL₀ : L₀ ≤ L := by have := le_max_left L₀ C; dsimp [L] <;> linarith
  have hLp : 0 < L := by linarith
  have hstrip := (dedekindXiZeros_re_mem_Icc_totallyReal σ hn hz).2
  have hX : 0 ≤ L * (1 - z.re) := mul_nonneg hLp.le (sub_nonneg.mpr hstrip)
  by_contra hgap
  have hsmall : (L * (1 - z.re)) ^ 2 + (L * z.im) ^ 2 < c ^ 2 := lt_of_not_ge hgap
  have hxc : L * (1 - z.re) < c := by nlinarith [sq_nonneg (L * z.im)]
  have hyc : |L * z.im| < c := by
    nlinarith [sq_nonneg (L * (1 - z.re)), sq_abs (L * z.im), abs_nonneg (L * z.im)]
  have hca : c ≤ a := min_le_left _ _
  have hcq : c ≤ 1 / 4 := min_le_right _ _
  have hbox : InNearOneBox L z := by
    constructor
    · have hx : 1 - z.re ≤ (1 / 4 : ℝ) / L :=
        (le_div_iff₀ hLp).mpr (by nlinarith only [hxc, hcq])
      have he : (1 / 4 : ℝ) / L = 1 / (4 * L) := by ring
      rw [he] at hx
      linarith
    · rw [abs_mul, abs_of_pos hLp] at hyc
      have hy : |z.im| ≤ (1 / 4 : ℝ) / L :=
        (le_div_iff₀ hLp).mpr (by nlinarith only [hyc, hcq])
      convert hy using 1
      all_goals try with_reducible_and_instances rfl
      ring
  obtain ⟨_, hreal, _⟩ := Hunique σ hn hLC z hz hbox
  have he : z = (z.re : ℂ) := by apply Complex.ext <;> simp [hreal]
  have hβlt : z.re < 1 := by
    apply lt_of_le_of_ne hstrip
    intro h
    have hz1 : z = 1 := by rw [he, h]; rfl
    subst z
    exact dedekindXiZeros_ne_one_totallyReal σ hn hz
  have hβlo : 1 - a / L ≤ z.re := by
    have hx : 1 - z.re ≤ a / L :=
      (le_div_iff₀ hLp).mpr (by nlinarith only [hxc, hca])
    linarith
  exact Hex K hn σ hLL₀ z.re hβlo hβlt (by simpa only [← he] using hz)

end DukePrimeDegree

end OAI
end

theorem solution.{u} : type_of% @OAI.DukePrimeDegree.completedXiGap_of_exceptionalRealZeroExclusion_oai.{u} := @OAI.DukePrimeDegree.completedXiGap_of_exceptionalRealZeroExclusion_oai.{u}
