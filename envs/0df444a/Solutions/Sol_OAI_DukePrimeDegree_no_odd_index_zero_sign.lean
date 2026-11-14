-- Prove2me | solution 1 for OAI.DukePrimeDegree.no_odd_index_zero_sign
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T06:42:50.048208+00:00
-- url     : https://prove2.me/submissions/62121221-63fa-4ab0-b17e-3a71f8eeb379

import Mathlib
import Mathlib.Algebra.Module.Submodule.RestrictScalars
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.RingTheory.Discriminant
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.Localization.Module
import Definitions.Def_DukePrimeDegree
import Definitions.Def_OAIQ244Duke023
import Definitions.Def_OAIQ244Duke024
import Theorems.Thm_OAI_PrimeDegreePackets_HeckeMellin_completedThetaXi_eq_totallyReal

section
-- module Solutions.OAIQ244_DUKE.Compat
attribute [-instance] _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.xMeasurableSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h
end OAICompat434

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
-- module Solutions.OAIQ244_DUKE.PrimePackets_ZetaResidues
attribute [-instance] _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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
-- module Solutions.OAIQ244_DUKE.PrimePackets_CharacterPairs
attribute [-instance] _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space
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
namespace PrimeDegreePackets

lemma realFiniteCharacter_values {G : Type*} [Group G] [Finite G]
    (χ : G →* ℝˣ) (g : G) : χ g = 1 ∨ χ g = -1 := by
  have hn := (((Units.coeHom ℝ).comp χ).isOfFinOrder
    (isOfFinOrder_of_finite g)).norm_eq_one
  change ‖(χ g : ℝ)‖ = 1 at hn
  rw [Real.norm_eq_abs] at hn
  rcases (abs_eq (show (0:ℝ) ≤ 1 by norm_num)).mp hn with h|h
  · exact Or.inl (Units.ext h)
  · exact Or.inr (Units.ext h)

 

lemma realFiniteCharacter_kernel_index {G : Type*} [Group G] [Finite G]
    (χ : G →* ℝˣ) {g : G} (hg : χ g ≠ 1) : χ.ker.index = 2 := by
  have hgm : χ g = -1 := (realFiniteCharacter_values χ g).resolve_left hg
  rw [Subgroup.index_ker]
  apply Nat.card_eq_two_iff.mpr
  let a : χ.range := ⟨1,⟨1,χ.map_one⟩⟩
  let b : χ.range := ⟨-1,⟨g,hgm⟩⟩
  refine ⟨a,b,?_,?_⟩
  · intro h
    have h' := congrArg (fun z : χ.range => ((z : ℝˣ) : ℝ)) h
    change (1:ℝ) = -1 at h'
    norm_num at h'
  · ext x
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff,Set.mem_univ,iff_true]
    obtain ⟨t,ht⟩ := x.property
    rcases realFiniteCharacter_values χ t with h|h
    · left; apply Subtype.ext; exact ht.symm.trans h
    · right; apply Subtype.ext; exact ht.symm.trans h

lemma realFiniteCharacter_trivial_of_odd_index {G : Type*} [Group G] [Finite G]
    (χ : G →* ℝˣ) (H : Subgroup G) (hodd : Odd H.index) (hH : H ≤ χ.ker) :
    ∀ g, χ g = 1 := by
  intro g
  by_contra hg
  have hdiv := Subgroup.index_dvd_of_le hH
  rw [realFiniteCharacter_kernel_index χ hg] at hdiv
  obtain ⟨k,hk⟩ := hodd
  obtain ⟨l,hl⟩ := hdiv
  omega



end PrimeDegreePackets

open MeasureTheory Module Set Filter
open scoped BigOperators ENNReal RealInnerProductSpace
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_RootOverlaps
attribute [-instance] _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.finiteIdeleGroupT2Space _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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

lemma completionExponential_hasDerivAt (n : ℕ) (D : ℝ) (s : ℂ) :
    HasDerivAt (completionExponential n D)
      (completionExponential n D s *
        (((Real.log D : ℝ) : ℂ) - n * (Real.log Real.pi : ℂ))/2) s := by
  have h := (((hasDerivAt_id s).mul_const
    (((Real.log D : ℝ) : ℂ) - n * (Real.log Real.pi : ℂ))).div_const 2).cexp
  change HasDerivAt (fun z : ℂ => Complex.exp
    (z * ((Real.log D : ℂ)-n*(Real.log Real.pi : ℂ))/2))
    (Complex.exp (s*((Real.log D : ℂ)-n*(Real.log Real.pi : ℂ))/2)*
      ((Real.log D : ℂ)-n*(Real.log Real.pi : ℂ))/2) s
  simpa only [one_mul,mul_div_assoc,id_eq] using h

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
-- module Solutions.OAIQ244_DUKE.PrimePackets_CoordinateLattices
attribute [-instance] _root_.CyclicCohomology.permutationSublattice_discreteTopology _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.circleMeasurableSpace OAI.circleBorelSpace

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
namespace PrimeDegreePackets.ThetaConstruction
variable {d : Type*} [Fintype d]

omit [Fintype d] in
lemma integerVector_closedEmbedding : IsClosedEmbedding (integerVector (d := d)) := by
  exact IsClosedEmbedding.piMap (fun _ => Int.isClosedEmbedding_coe_real)

lemma integerVector_tendsto : Tendsto (integerVector (d := d)) cofinite (cocompact _) := by
  simpa only [cocompact_eq_cofinite] using (integerVector_closedEmbedding (d := d)).tendsto_cocompact

lemma integerVectorInLattice_injective : Function.Injective (integerVectorInLattice (d := d)) := by
  intro z w h
  have hv := congrArg Subtype.val h
  ext i
  exact Int.cast_injective (congrFun hv i)

lemma coordinateLattice_rank : Module.finrank ℤ (coordinateLattice (d := d)) = Fintype.card d := by
  rw [ZLattice.rank ℝ (coordinateLattice (d := d))]
  simp

lemma summable_integerVector_rpow {r : ℝ} (hr : r < -(Fintype.card d : ℝ)) :
    Summable (fun z : d → ℤ => ‖integerVector z‖ ^ r) := by
  have hr' : r < -(Module.finrank ℤ (coordinateLattice (d := d)) : ℝ) := by
    simpa only [coordinateLattice_rank] using hr
  have H := ZLattice.summable_norm_rpow (coordinateLattice (d := d)) r hr'
  exact H.comp_injective (i := integerVectorInLattice (d := d))
    (integerVectorInLattice_injective (d := d))

end PrimeDegreePackets.ThetaConstruction

open MeasureTheory Set Filter Topology Module WithLp
open scoped BigOperators SchwartzMap ZeroAtInfty
namespace PrimeDegreePackets.ThetaConstruction
variable {d : Type*} [Fintype d]

 

lemma locallyNormal_of_polynomial_decay (f : C(d → ℝ,ℂ)) (p : ℕ)
    (hp : Fintype.card d < p) (C : ℝ) (hC : 0 < C)
    (hdecay : ∀ x, ‖x‖^p * ‖f x‖ ≤ C) : LocallyNormal f := by
  intro K
  obtain ⟨R,hR⟩ := K.isCompact.isBounded.subset_closedBall 0
  have hsum : Summable (fun z : d → ℤ => C * 2^p * ‖integerVector z‖ ^ (-(p:ℝ))) :=
    (summable_integerVector_rpow (by apply neg_lt_neg; exact_mod_cast hp)).mul_left _
  apply Summable.of_norm_bounded_eventually hsum
  have hz : ∀ᶠ z : d → ℤ in cofinite, 2*|R|+1 < ‖integerVector z‖ := by
    exact ((tendsto_norm_cocompact_atTop (E := d → ℝ)).comp
      (integerVector_tendsto (d := d))).eventually (eventually_gt_atTop (2*|R|+1))
  filter_upwards [hz] with z hz
  rw [norm_norm]
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  rintro ⟨x,hx⟩
  change ‖f (x + integerVector z)‖ ≤ C * 2^p * ‖integerVector z‖ ^ (-(p:ℝ))
  have hxR : ‖x‖ ≤ R := by simpa using hR hx
  have hzpos : 0 < ‖integerVector z‖ := by linarith [abs_nonneg R]
  have htri := norm_sub_le (x + integerVector z) x
  have hzle : ‖integerVector z‖/2 ≤ ‖x + integerVector z‖ := by
    simp only [add_sub_cancel_left] at htri
    linarith [le_abs_self R]
  have hwpos : 0 < ‖x + integerVector z‖ := lt_of_lt_of_le (by positivity) hzle
  have hbound : (‖integerVector z‖/2)^p * ‖f (x+integerVector z)‖ ≤ C :=
    (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hzle _) (norm_nonneg _)).trans
      (hdecay _)
  rw [Real.rpow_neg (norm_nonneg _),Real.rpow_natCast]
  apply (le_mul_inv_iff₀ (pow_pos hzpos p)).mpr
  rw [div_pow] at hbound
  have H := (div_le_iff₀ (by positivity : 0 < (2:ℝ)^p)).mp
    (show ‖f (x+integerVector z)‖ * ‖integerVector z‖^p / 2^p ≤ C by
      simpa only [div_mul_eq_mul_div,mul_comm] using hbound)
  exact H

lemma gaussian_polynomial_bound (b : ℝ) (hb : 0 < b) (p : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, |t|^p * Real.exp (-b*t^2) ≤ C := by
  let h : C₀(ℝ,ℝ) := {
    toFun t := |t|^p * Real.exp (-b*t^2)
    continuous_toFun := by fun_prop
    zero_at_infty' := by
      simpa only [Real.rpow_natCast] using
        tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact hb (p:ℝ) }
  refine ⟨‖h.toBCF‖+1,by positivity,fun t => ?_⟩
  have H := BoundedContinuousFunction.norm_coe_le_norm h.toBCF t
  exact (le_abs_self (h t)).trans (H.trans (by linarith))

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma coordinateGaussian_decay (A : (d → ℝ) ≃L[ℝ] E) (b : ℝ) (hb : 0 < b) (p : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x, ‖x‖^p * ‖coordinateGaussian A b x‖ ≤ C := by
  obtain ⟨C,hC,hbound⟩ := gaussian_polynomial_bound b hb p
  let B := ‖A.symm.toContinuousLinearMap‖ + 1
  have hB : 0 < B := by dsimp [B] <;> positivity
  refine ⟨B^p*C,by positivity,fun x => ?_⟩
  have hx : ‖x‖ ≤ B * ‖A x‖ := by
    have H := A.symm.toContinuousLinearMap.le_opNorm (A x)
    simp only [ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.symm_apply_apply] at H
    exact H.trans (by dsimp [B] <;> nlinarith [norm_nonneg (A x)])
  have hnorm : ‖coordinateGaussian A b x‖ = Real.exp (-b*‖A x‖^2) := by
    simp [coordinateGaussian,Complex.norm_exp,pow_two]
  rw [hnorm]
  calc
    _ ≤ (B*‖A x‖)^p * Real.exp (-b*‖A x‖^2) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hx _) (Real.exp_nonneg _)
    _ = B^p * (‖A x‖^p * Real.exp (-b*‖A x‖^2)) := by rw [mul_pow,mul_assoc]
    _ ≤ B^p*C := mul_le_mul_of_nonneg_left (by simpa only [abs_norm] using hbound ‖A x‖)
      (pow_nonneg hB.le _)

lemma coordinateGaussian_locallyNormal (A : (d → ℝ) ≃L[ℝ] E) (b : ℝ) (hb : 0 < b) :
    LocallyNormal (coordinateGaussian A b) := by
  obtain ⟨C,hC,hdecay⟩ := coordinateGaussian_decay A b hb (Fintype.card d + 1)
  exact locallyNormal_of_polynomial_decay _ _ (Nat.lt_succ_self _) C hC hdecay

end PrimeDegreePackets.ThetaConstruction

open scoped FourierTransform

open scoped BigOperators SchwartzMap FourierTransform

open scoped BigOperators FourierTransform
namespace PrimeDegreePackets.ThetaConstruction
variable {d : Type*} [Fintype d]



lemma summable_of_locallyNormal (f : C(d → ℝ,ℂ)) (hf : LocallyNormal f) :
    Summable (fun z : d → ℤ => f (integerVector z)) := by
  have H := ContinuousMap.summable_of_locally_summable_norm hf
  have H' := (ContinuousMap.evalCLM ℂ (x := (0:d→ℝ))).summable H
  simpa [translate] using H'

lemma latticeTheta_summable (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (b : ℝ) (hb : 0 < b) :
    Summable (fun z : d → ℤ => Complex.exp (-(b:ℂ) * ‖B (euclideanInteger z)‖^2)) := by
  exact summable_of_locallyNormal (coordinateGaussian (coordinateBasis B) b)
    (coordinateGaussian_locallyNormal _ b hb)

end PrimeDegreePackets.ThetaConstruction

open MeasureTheory Set Filter Topology Module WithLp Asymptotics
namespace PrimeDegreePackets.ThetaConstruction
variable {d : Type*} [Fintype d]

lemma thetaRemainder_summable (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    {t : ℝ} (ht : 0 < t) : Summable (fun z : NonzeroIntegerVector d =>
      Complex.exp (-(t:ℂ) * ‖B (euclideanInteger z.1)‖^2)) :=
  (latticeTheta_summable B t ht).subtype _

lemma gaussianTerm_norm (t r : ℝ) :
    ‖Complex.exp (-(t:ℂ) * (r:ℂ)^2)‖ = Real.exp (-t*r^2) := by
  simp [Complex.norm_exp,pow_two]

lemma euclideanInteger_norm_one_le (z : NonzeroIntegerVector d) :
    1 ≤ ‖euclideanInteger z.1‖ := by
  obtain ⟨i,hi⟩ : ∃ i, z.1 i ≠ 0 := by
    by_contra! H
    exact z.2 (funext H)
  have H : (1:ℝ) ≤ |(z.1 i:ℝ)| := by exact_mod_cast Int.one_le_abs hi
  exact H.trans (by simpa [euclideanInteger,integerVector,Real.norm_eq_abs] using
    PiLp.norm_apply_le (euclideanInteger z.1) i)

end PrimeDegreePackets.ThetaConstruction
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_LatticeTheta
attribute [-instance] _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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

lemma fullLatticeEuclideanBasis_det (M : FullLattice n K) (σ : OrderedEmbeddings n K)
    (hn : Module.finrank ℚ K = n) :
    LinearMap.det (fullLatticeEuclideanBasis M σ hn).toLinearMap = (embeddingMatrix M σ).det := by
  change LinearMap.det ((Matrix.toLin (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis) (embeddingMatrix M σ).transpose) = _
  rw [LinearMap.det_toLin,Matrix.det_transpose]

end PrimeDegreePackets


open Module MeasureTheory
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_ThetaTails
attribute [-instance] _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.finiteIdeleGroupT2Space _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space
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
namespace PrimeDegreePackets.ThetaConstruction
variable {d : Type*} [Fintype d]

 

theorem thetaRemainder_uniform_exponential_bound (R : ℝ) (hR : 0 ≤ R) :
    ∃ a C : ℝ, 0 < a ∧ 0 ≤ C ∧
      ∀ (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d),
        ‖B.symm.toContinuousLinearMap‖ ≤ R → ∀ t : ℝ, 1 ≤ t →
          ‖thetaRemainder B t‖ ≤ C * Real.exp (-a*t) := by
  let c : ℝ := (R+1)⁻¹
  have hc : 0 < c := inv_pos.mpr (by linarith)
  let a : ℝ := c^2/2
  have ha : 0 < a := by dsimp [a] <;> positivity
  let v := fun z : NonzeroIntegerVector d => Real.exp (-a*‖euclideanInteger z.1‖^2)
  have hv : Summable v := by
    have H := (thetaRemainder_summable (ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ d)) ha).norm
    simpa only [ContinuousLinearEquiv.refl_apply,gaussianTerm_norm] using H
  refine ⟨a,∑' z, v z,ha,tsum_nonneg (fun z => (Real.exp_pos _).le),fun B hB t ht => ?_⟩
  have hbound (z : NonzeroIntegerVector d) : c*‖euclideanInteger z.1‖ ≤ ‖B (euclideanInteger z.1)‖ := by
    have H := B.symm.toContinuousLinearMap.le_opNorm (B (euclideanInteger z.1))
    simp only [ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.symm_apply_apply] at H
    have HR : 0 < R+1 := by linarith
    rw [show c*‖euclideanInteger z.1‖ = ‖euclideanInteger z.1‖/(R+1) by dsimp [c]; ring,
      div_le_iff₀ HR]
    calc
      ‖euclideanInteger z.1‖ ≤ ‖B.symm.toContinuousLinearMap‖ * ‖B (euclideanInteger z.1)‖ := H
      _ ≤ ‖B (euclideanInteger z.1)‖*(R+1) := by nlinarith [norm_nonneg (B (euclideanInteger z.1))]
  have ht' : 0 < t := by linarith
  calc
    ‖thetaRemainder B t‖ ≤ ∑' z : NonzeroIntegerVector d,
        ‖Complex.exp (-(t:ℂ)*‖B (euclideanInteger z.1)‖^2)‖ :=
      norm_tsum_le_tsum_norm (thetaRemainder_summable B ht').norm
    _ ≤ ∑' z, v z * Real.exp (-a*t) := by
      apply (thetaRemainder_summable B ht').norm.tsum_le_tsum _ (hv.mul_right _)
      intro z
      rw [gaussianTerm_norm]
      dsimp only [v]
      rw [←Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hx := euclideanInteger_norm_one_le z
      have hy := hbound z
      have hx2 : 1 ≤ ‖euclideanInteger z.1‖^2 := by nlinarith
      have hcsq : c^2 * ‖euclideanInteger z.1‖^2 ≤ ‖B (euclideanInteger z.1)‖^2 := by
        have H := (sq_le_sq₀ (mul_nonneg hc.le (norm_nonneg _)) (norm_nonneg _)).mpr hy
        simpa only [mul_pow] using H
      have h1 := mul_nonneg (sub_nonneg.mpr ht) (mul_nonneg (sq_nonneg c)
        (sq_nonneg ‖euclideanInteger z.1‖))
      have h2 := mul_nonneg ht'.le (sub_nonneg.mpr hcsq)
      have h3 := mul_nonneg (sq_nonneg c) (sub_nonneg.mpr hx2)
      have h4 := mul_nonneg ht'.le h3
      dsimp only [a]
      nlinarith
    _ = _ := tsum_mul_right

end PrimeDegreePackets.ThetaConstruction


namespace PrimeDegreePackets.ThetaConstruction
variable {d : Type*} [Fintype d]
variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
variable (B : α → EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)

omit [IsFiniteMeasure μ] in
lemma normalizedThetaTail_joint_stronglyMeasurable
    (hB : ∀ z : d → ℤ, Measurable (fun x => B x (euclideanInteger z))) :
    StronglyMeasurable (fun p : α × ℝ => normalizedThetaTail (B p.1) p.2) := by
  have HH : Measurable (fun p : α × ℝ => thetaRemainder (B p.1) (Real.pi*max p.2 1)) := by
    unfold thetaRemainder
    apply Measurable.tsum
    intro z
    have HB : Measurable (fun p : α × ℝ => B p.1 (euclideanInteger z.1)) :=
      (hB z.1).comp measurable_fst
    fun_prop
  have HP : MeasurableSet {p : α × ℝ | 1 < p.2} :=
    measurableSet_lt measurable_const measurable_snd
  apply Measurable.stronglyMeasurable
  convert HH.indicator HP using 1
  all_goals try with_reducible_and_instances rfl
  ext p
  simp only [normalizedThetaTail,Set.indicator_apply]
  rfl


omit [IsFiniteMeasure μ] in
lemma averagedNormalizedThetaTail_eq_zero {t : ℝ} (ht : t ≤ 1) :
    averagedNormalizedThetaTail μ B t = 0 := by
  simp [averagedNormalizedThetaTail,normalizedThetaTail,not_lt.mpr ht]

lemma averagedNormalizedThetaTail_stronglyMeasurable
    (hB : StronglyMeasurable (fun p : α × ℝ => normalizedThetaTail (B p.1) p.2)) :
    StronglyMeasurable (averagedNormalizedThetaTail μ B) :=
  hB.integral_prod_left'

lemma averagedNormalizedThetaTail_bounds (R : ℝ) (hR : 0 ≤ R)
    (hB : ∀ x, ‖(B x).symm.toContinuousLinearMap‖ ≤ R) :
    ∃ a C : ℝ, 0 < a ∧ 0 ≤ C ∧
      (∀ t : ℝ, ‖averagedNormalizedThetaTail μ B t‖ ≤ C) ∧
      ∀ t : ℝ, 1 < t → ‖averagedNormalizedThetaTail μ B t‖ ≤ C * Real.exp (-a*t) := by
  obtain ⟨a,C,ha,hC,hbound⟩ := thetaRemainder_uniform_exponential_bound (d := d) R hR
  have Hb (t : ℝ) (ht : 1 < t) :
      ‖averagedNormalizedThetaTail μ B t‖ ≤ (C*μ.real Set.univ) * Real.exp (-(a*Real.pi)*t) := by
    have HP : 1 ≤ Real.pi*t := by nlinarith [Real.pi_gt_three]
    have HH := norm_integral_le_of_norm_le_const (μ := μ)
      (Filter.Eventually.of_forall (fun x => hbound (B x) (hB x) (Real.pi*t) HP))
    have HE : averagedNormalizedThetaTail μ B t = ∫ x, thetaRemainder (B x) (Real.pi*t) ∂μ := by
      simp only [averagedNormalizedThetaTail,normalizedThetaTail,
        Set.indicator_of_mem (show t ∈ Set.Ioi 1 from ht),max_eq_left ht.le]
    rw [HE]
    rw [show -a*(Real.pi*t) = -(a*Real.pi)*t by ring] at HH
    simpa only [mul_assoc,mul_left_comm,mul_comm] using HH
  refine ⟨a*Real.pi,C*μ.real Set.univ,mul_pos ha Real.pi_pos,
    mul_nonneg hC (measureReal_nonneg),?_,Hb⟩
  intro t
  by_cases ht : 1 < t
  · apply (Hb t ht).trans
    apply mul_le_of_le_one_right (mul_nonneg hC (measureReal_nonneg))
    rw [Real.exp_le_one_iff]
    have := mul_pos (mul_pos ha Real.pi_pos) (zero_lt_one.trans ht)
    nlinarith
  · rw [averagedNormalizedThetaTail_eq_zero μ B (not_lt.mp ht),norm_zero]
    positivity

lemma averagedNormalizedThetaTail_locallyIntegrable (R : ℝ) (hR : 0 ≤ R)
    (hbound : ∀ x, ‖(B x).symm.toContinuousLinearMap‖ ≤ R)
    (hB : StronglyMeasurable (fun p : α × ℝ => normalizedThetaTail (B p.1) p.2)) :
    LocallyIntegrable (averagedNormalizedThetaTail μ B) := by
  obtain ⟨a,C,ha,hC,hall,_⟩ := averagedNormalizedThetaTail_bounds μ B R hR hbound
  rw [locallyIntegrable_iff]
  intro k hk
  have : IsFiniteMeasure (volume.restrict k) := isFiniteMeasure_restrict.mpr hk.measure_lt_top.ne
  exact (integrable_const C).mono'
    (averagedNormalizedThetaTail_stronglyMeasurable μ B hB).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun t => hall t))

omit [IsFiniteMeasure μ] in
lemma averagedNormalizedThetaTail_bigO_zero (b : ℝ) :
    averagedNormalizedThetaTail μ B =O[𝓝[>] 0] (fun t : ℝ => t^(-b)) := by
  apply IsBigO.of_bound 0
  have H : ∀ᶠ t : ℝ in 𝓝[>] 0, t < 1 :=
    eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds zero_lt_one)
  filter_upwards [H] with t ht
  simp [averagedNormalizedThetaTail_eq_zero μ B ht.le]

 

theorem averagedNormalizedThetaTail_mellin_differentiable (R : ℝ) (hR : 0 ≤ R)
    (hbound : ∀ x, ‖(B x).symm.toContinuousLinearMap‖ ≤ R)
    (hB : StronglyMeasurable (fun p : α × ℝ => normalizedThetaTail (B p.1) p.2)) :
    Differentiable ℂ (mellin (averagedNormalizedThetaTail μ B)) := by
  obtain ⟨a,C,ha,_,_,hdecay⟩ := averagedNormalizedThetaTail_bounds μ B R hR hbound
  have Hdecay : averagedNormalizedThetaTail μ B =O[atTop] (fun t => Real.exp (-a*t)) := by
    apply IsBigO.of_bound C
    filter_upwards [eventually_gt_atTop (1:ℝ)] with t ht
    simpa only [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] using hdecay t ht
  intro s
  exact mellin_differentiableAt_of_isBigO_rpow_exp ha
    ((averagedNormalizedThetaTail_locallyIntegrable μ B R hR hbound hB).locallyIntegrableOn (Set.Ioi 0))
    Hdecay (averagedNormalizedThetaTail_bigO_zero μ B (s.re-1)) (by linarith)

end PrimeDegreePackets.ThetaConstruction


namespace PrimeDegreePackets.ThetaConstruction
variable {d : Type*} [Fintype d]


lemma logScale_symm (u : d → ℝ) : (logScale u).symm = logScale (-u) := by
  ext x i
  rfl

lemma logScale_norm_le {u : d → ℝ} {R : ℝ} (hR : ∀ i, u i ≤ R)
    (x : EuclideanSpace ℝ d) : ‖logScale u x‖ ≤ Real.exp R*‖x‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))).mp
  rw [mul_pow,EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [logScale_apply,mul_pow]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact (sq_le_sq₀ (Real.exp_pos _).le (Real.exp_pos _).le).mpr (Real.exp_le_exp.mpr (hR i))

lemma logScaledLattice_inverse_bound (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    {u : d → ℝ} {R : ℝ} (hR : ∀ i, -u i ≤ R) :
    ‖(logScaledLattice B u).symm.toContinuousLinearMap‖ ≤
      ‖B.symm.toContinuousLinearMap‖*Real.exp R := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)
  intro x
  change ‖B.symm ((logScale u).symm x)‖ ≤ _
  calc
    _ ≤ ‖B.symm.toContinuousLinearMap‖*‖(logScale u).symm x‖ :=
      B.symm.toContinuousLinearMap.le_opNorm _
    _ ≤ ‖B.symm.toContinuousLinearMap‖*(Real.exp R*‖x‖) := by
      gcongr
      rw [logScale_symm]
      exact logScale_norm_le hR x
    _ = _ := by ring

lemma logScaledLattice_measurable_apply {α : Type*} [MeasurableSpace α]
    (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d) (u : α → d → ℝ)
    (hu : ∀ i, Measurable (fun a => u a i)) (x : EuclideanSpace ℝ d) :
    Measurable (fun a => logScaledLattice B (u a) x) := by
  change Measurable (fun a => toLp 2 (fun i => Real.exp (u a i)*(B x) i))
  exact (PiLp.continuous_toLp 2 (fun _ : d => ℝ)).measurable.comp (Measurable.of_eval (fun i =>
    ((hu i).exp).mul_const _))



end PrimeDegreePackets.ThetaConstruction


namespace PrimeDegreePackets
open ThetaConstruction


lemma restoredLogCoordinates_continuous {d : ℕ} (i : Fin (d+1)) :
    Continuous (fun u : LogCoordinates d => restoredLogCoordinates u i) := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [restoredLogCoordinates,Fin.snoc_last]
    fun_prop
  · simp only [restoredLogCoordinates,Fin.snoc_castSucc]
    exact continuous_apply j

end PrimeDegreePackets


namespace PrimeDegreePackets.ThetaConstruction
variable {d : Type*} [Fintype d]

lemma exponentialTail_mellinConvergent {a : ℝ} (ha : 0 < a) (s : ℂ) :
    MellinConvergent (exponentialTail a) s := by
  have HL : LocallyIntegrable (exponentialTail a) :=
    (show Continuous (fun t : ℝ => (Real.exp (-a*t):ℂ)) by fun_prop).locallyIntegrable.indicator
      measurableSet_Ioi
  have HE : exponentialTail a =O[atTop] (fun t => Real.exp (-a*t)) := by
    apply IsBigO.of_bound 1
    filter_upwards [eventually_gt_atTop (1:ℝ)] with t ht
    simp [exponentialTail,ht,Complex.norm_exp]
  have HZ : exponentialTail a =O[𝓝[>] 0] (fun t : ℝ => t^(-(s.re-1))) := by
    apply IsBigO.of_bound 0
    have H : ∀ᶠ t : ℝ in 𝓝[>] 0, t < 1 :=
      eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds zero_lt_one)
    filter_upwards [H] with t ht
    simp [exponentialTail,not_lt.mpr ht.le]
  exact mellinConvergent_of_isBigO_rpow_exp ha (HL.locallyIntegrableOn (Set.Ioi 0)) HE HZ (by linarith)

lemma normalizedThetaTail_uniform_majorant (R : ℝ) (hR : 0 ≤ R) :
    ∃ a C : ℝ, 0 < a ∧ 0 ≤ C ∧
      ∀ (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d),
        ‖B.symm.toContinuousLinearMap‖ ≤ R → ∀ t : ℝ,
          ‖normalizedThetaTail B t‖ ≤ C * ‖exponentialTail a t‖ := by
  obtain ⟨a,C,ha,hC,hbound⟩ := thetaRemainder_uniform_exponential_bound (d := d) R hR
  refine ⟨a*Real.pi,C,mul_pos ha Real.pi_pos,hC,fun B hB t => ?_⟩
  by_cases ht : 1 < t
  · have H := hbound B hB (Real.pi*t) (by nlinarith [Real.pi_gt_three])
    simpa [normalizedThetaTail,exponentialTail,ht,max_eq_left ht.le,
      Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),mul_assoc,Complex.norm_exp] using H
  · simp [normalizedThetaTail,exponentialTail,ht]

 
theorem normalizedThetaTail_mellin_integrableProd
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (B : α → EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (R : ℝ) (hR : 0 ≤ R) (hbound : ∀ x, ‖(B x).symm.toContinuousLinearMap‖ ≤ R)
    (hB : StronglyMeasurable (fun p : α × ℝ => normalizedThetaTail (B p.1) p.2)) (s : ℂ) :
    Integrable (fun p : α × ℝ => (p.2:ℂ)^(s-1) * normalizedThetaTail (B p.1) p.2)
      (μ.prod (volume.restrict (Set.Ioi 0))) := by
  let ν : Measure ℝ := volume.restrict (Set.Ioi 0)
  obtain ⟨a,C,ha,_,hmajorant⟩ := normalizedThetaTail_uniform_majorant (d := d) R hR
  let F : α × ℝ → ℂ := fun p => (p.2:ℂ)^(s-1) * normalizedThetaTail (B p.1) p.2
  let g : ℝ → ℂ := fun t => (t:ℂ)^(s-1) * exponentialTail a t
  have hg : Integrable g ν := exponentialTail_mellinConvergent ha s
  have hF : AEStronglyMeasurable F (μ.prod ν) := by
    apply StronglyMeasurable.aestronglyMeasurable
    exact ((Complex.measurable_ofReal.comp measurable_snd).pow_const (s-1)).stronglyMeasurable.mul hB
  have HF : Integrable F (μ.prod ν) := by
    apply ((integrable_const C).mul_prod hg.norm).mono' hF
    apply Filter.Eventually.of_forall
    intro p
    change ‖(p.2:ℂ)^(s-1) * normalizedThetaTail (B p.1) p.2‖ ≤
      C * ‖(p.2:ℂ)^(s-1) * exponentialTail a p.2‖
    simp only [norm_mul]
    calc
      _ ≤ ‖(p.2:ℂ)^(s-1)‖*(C*‖exponentialTail a p.2‖) :=
        mul_le_mul_of_nonneg_left (hmajorant (B p.1) (hbound p.1) p.2) (norm_nonneg _)
      _ = _ := by ring
  exact HF

lemma normalizedThetaTail_mellin_integrable
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (B : α → EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (R : ℝ) (hR : 0 ≤ R) (hbound : ∀ x, ‖(B x).symm.toContinuousLinearMap‖ ≤ R)
    (hB : StronglyMeasurable (fun p : α × ℝ => normalizedThetaTail (B p.1) p.2)) (s : ℂ) :
    Integrable (fun x => mellin (normalizedThetaTail (B x)) s) μ := by
  simpa only [mellin,smul_eq_mul] using
    (normalizedThetaTail_mellin_integrableProd μ B R hR hbound hB s).integral_prod_left

 

theorem averagedNormalizedThetaTail_mellin_eq_integral
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (B : α → EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (R : ℝ) (hR : 0 ≤ R) (hbound : ∀ x, ‖(B x).symm.toContinuousLinearMap‖ ≤ R)
    (hB : StronglyMeasurable (fun p : α × ℝ => normalizedThetaTail (B p.1) p.2)) (s : ℂ) :
    mellin (averagedNormalizedThetaTail μ B) s =
      ∫ x, mellin (normalizedThetaTail (B x)) s ∂μ := by
  let ν : Measure ℝ := volume.restrict (Set.Ioi 0)
  have HF := normalizedThetaTail_mellin_integrableProd μ B R hR hbound hB s
  calc
    mellin (averagedNormalizedThetaTail μ B) s =
        ∫ t, ∫ x, (t:ℂ)^(s-1) * normalizedThetaTail (B x) t ∂μ ∂ν := by
      unfold mellin averagedNormalizedThetaTail
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun t => (integral_const_mul _ _).symm)
    _ = ∫ x, ∫ t, (t:ℂ)^(s-1) * normalizedThetaTail (B x) t ∂ν ∂μ :=
      (integral_integral_swap HF).symm
    _ = _ := rfl

end PrimeDegreePackets.ThetaConstruction
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_LatticeDuality
attribute [-instance] _root_.CyclicCohomology.permutationSublattice_discreteTopology _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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
namespace PrimeDegreePackets.ThetaConstruction
variable {d : Type*} [Fintype d]

lemma logScale_selfAdjoint (u : d → ℝ) :
    (logScale u).toContinuousLinearMap.adjoint = (logScale u).toContinuousLinearMap := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  simp only [PiLp.inner_apply,ContinuousLinearEquiv.coe_coe,logScale_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp [mul_assoc,mul_left_comm,mul_comm]

lemma adjointEquiv_logScaledLattice (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (u : d → ℝ) :
    adjointEquiv (logScaledLattice B u).symm =
      logScaledLattice (adjointEquiv B.symm) (-u) := by
  have HE : (logScaledLattice B u).symm.toContinuousLinearMap =
      B.symm.toContinuousLinearMap.comp (logScale u).symm.toContinuousLinearMap := by
    ext x
    rfl
  apply ContinuousLinearEquiv.ext
  funext x
  change ((logScaledLattice B u).symm.toContinuousLinearMap.adjoint) x = _
  rw [HE,ContinuousLinearMap.adjoint_comp,logScale_symm,logScale_selfAdjoint]
  rfl

lemma logScale_det (u : d → ℝ) :
    LinearMap.det (logScale u).toLinearMap = Real.exp (∑ i, u i) := by
  classical
  let b := (EuclideanSpace.basisFun d ℝ).toBasis
  have HE : (logScale u).toLinearMap = Matrix.toLin b b (Matrix.diagonal (fun i => Real.exp (u i))) := by
    ext x i
    rw [Matrix.toLin_apply]
    simp [b,EuclideanSpace.basisFun_apply,Matrix.mulVec,Matrix.diagonal_apply,Pi.single_apply,dotProduct]
  rw [HE,LinearMap.det_toLin,Matrix.det_diagonal,Real.exp_sum]

lemma logScaledLattice_det (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (u : d → ℝ) :
    LinearMap.det (logScaledLattice B u).toLinearMap =
      Real.exp (∑ i, u i) * LinearMap.det B.toLinearMap := by
  change LinearMap.det ((logScale u).toLinearMap.comp B.toLinearMap) = _
  rw [LinearMap.det_comp,logScale_det]

end PrimeDegreePackets.ThetaConstruction


namespace PrimeDegreePackets
open ThetaConstruction

lemma restoredLogCoordinates_sum {d : ℕ} (u : LogCoordinates d) :
    ∑ i, restoredLogCoordinates u i = 0 := by
  simp [restoredLogCoordinates,Fin.sum_univ_castSucc]

end PrimeDegreePackets


namespace PrimeDegreePackets.ThetaConstruction
variable {d : Type*} [Fintype d]

 

theorem averagedThetaMellinXi_differentiable
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (B : α → EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (R T : ℝ) (hR : 0 ≤ R) (hT : 0 ≤ T)
    (hbound : ∀ x, ‖(B x).symm.toContinuousLinearMap‖ ≤ R)
    (hdual : ∀ x, ‖(adjointEquiv (B x).symm).symm.toContinuousLinearMap‖ ≤ T)
    (hB : StronglyMeasurable (fun p : α × ℝ => normalizedThetaTail (B p.1) p.2))
    (hD : StronglyMeasurable (fun p : α × ℝ =>
      normalizedThetaTail (adjointEquiv (B p.1).symm) p.2))
    (c : ℂ) (hc : ∀ x, ((|(LinearMap.det (B x).toLinearMap)⁻¹|:ℝ):ℂ) = c) :
    Differentiable ℂ (fun s => ∫ x, thetaMellinXi (B x) s ∂μ) := by
  let a : ℂ := (Fintype.card d:ℂ)/2
  let P := mellin (averagedNormalizedThetaTail μ B)
  let Q := mellin (averagedNormalizedThetaTail μ (fun x => adjointEquiv (B x).symm))
  have HP : Differentiable ℂ P := averagedNormalizedThetaTail_mellin_differentiable μ B R hR hbound hB
  have HQ : Differentiable ℂ Q := averagedNormalizedThetaTail_mellin_differentiable μ _ T hT hdual hD
  have HE : (fun s => ∫ x, thetaMellinXi (B x) s ∂μ) =
      fun s => s*(s-a)*(P s+c*Q (a-s)) + (μ.real Set.univ:ℂ)*(c*s-(s-a)) := by
    funext s
    have hP := normalizedThetaTail_mellin_integrable μ B R hR hbound hB s
    have hQ := normalizedThetaTail_mellin_integrable μ _ T hT hdual hD (a-s)
    have hQc : Integrable (fun x => c*mellin (normalizedThetaTail (adjointEquiv (B x).symm)) (a-s)) μ := hQ.const_mul c
    have hPQ : Integrable (fun x => mellin (normalizedThetaTail (B x)) s +
        c*mellin (normalizedThetaTail (adjointEquiv (B x).symm)) (a-s)) μ := hP.add hQc
    have hPQc : Integrable (fun x => s*(s-a)*(mellin (normalizedThetaTail (B x)) s +
        c*mellin (normalizedThetaTail (adjointEquiv (B x).symm)) (a-s))) μ := hPQ.const_mul _
    have HPv := averagedNormalizedThetaTail_mellin_eq_integral μ B R hR hbound hB s
    have HQv := averagedNormalizedThetaTail_mellin_eq_integral μ _ T hT hdual hD (a-s)
    calc
      (∫ x, thetaMellinXi (B x) s ∂μ) = ∫ x,
          s*(s-a)*(mellin (normalizedThetaTail (B x)) s +
            c*mellin (normalizedThetaTail (adjointEquiv (B x).symm)) (a-s)) +
          (c*s-(s-a)) ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun x => by simp only [thetaMellinXi,hc x]; dsimp [a] <;> ring)
      _ = s*(s-a)*(P s+c*Q (a-s)) + (μ.real Set.univ:ℂ)*(c*s-(s-a)) := by
        rw [integral_add hPQc (integrable_const (c*s-(s-a))),
          integral_const_mul,integral_add hP hQc,integral_const_mul,
          integral_const,←HPv,←HQv]
        simp only [P,Q,Complex.real_smul]
  rw [HE]
  fun_prop

end PrimeDegreePackets.ThetaConstruction


namespace PrimeDegreePackets
open ThetaConstruction

lemma restoredLogCoordinates_abs_bound_on_compact {d : ℕ} {S : Set (LogCoordinates d)}
    (hS : IsCompact S) : ∃ R : ℝ, ∀ u ∈ S, ∀ i, |restoredLogCoordinates u i| ≤ R := by
  let f : LogCoordinates d → ℝ := fun u => ∑ i, |restoredLogCoordinates u i|
  have hf : Continuous f := continuous_finsetSum _ (fun i _ =>
    (restoredLogCoordinates_continuous i).abs)
  obtain ⟨R,hR⟩ := hS.bddAbove_image hf.continuousOn
  refine ⟨R,fun u hu i => le_trans ?_ (hR (Set.mem_image_of_mem f hu))⟩
  change |restoredLogCoordinates u i| ≤ ∑ j, |restoredLogCoordinates u j|
  exact Finset.single_le_sum (fun j _ => abs_nonneg (restoredLogCoordinates u j)) (Finset.mem_univ i)

 

theorem arithmeticFlowThetaXi_boundedAverage_entire {d : ℕ} {K : Type*}
    [Field K] [NumberField K] (M : FullLattice (d+1) K)
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    {S : Set (LogCoordinates d)} (hS : MeasurableSet S) (hbd : Bornology.IsBounded S) :
    Differentiable ℂ (fun s => ∫ u in S,
      thetaMellinXi (logScaledLattice (fullLatticeEuclideanBasis M σ hn)
        (restoredLogCoordinates u)) s) := by
  let μ : Measure S := Measure.comap ((↑) : S → LogCoordinates d) volume
  have hμ : IsFiniteMeasure μ := ⟨by
    dsimp only [μ]
    rw [comap_subtype_coe_apply hS,Set.image_univ,Subtype.range_coe]
    exact hbd.measure_lt_top⟩
  let B := fullLatticeEuclideanBasis M σ hn
  let u : S → Fin (d+1) → ℝ := fun x => restoredLogCoordinates x.1
  let F := fun x : S => logScaledLattice B (u x)
  have hu : ∀ i, Measurable (fun x => u x i) := fun i =>
    ((restoredLogCoordinates_continuous i).comp continuous_subtype_val).measurable
  obtain ⟨U,hU⟩ := restoredLogCoordinates_abs_bound_on_compact hbd.isCompact_closure
  let R := ‖B.symm.toContinuousLinearMap‖*Real.exp U
  let T := ‖(adjointEquiv B.symm).symm.toContinuousLinearMap‖*Real.exp U
  have hR : 0 ≤ R := mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  have hT : 0 ≤ T := mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  have HB : ∀ x, ‖(F x).symm.toContinuousLinearMap‖ ≤ R := by
    intro x
    exact logScaledLattice_inverse_bound B (fun i =>
      (neg_le_abs _).trans (hU x.1 (subset_closure x.2) i))
  have HD : ∀ x, ‖(adjointEquiv (F x).symm).symm.toContinuousLinearMap‖ ≤ T := by
    intro x
    rw [show F x = logScaledLattice B (u x) from rfl,adjointEquiv_logScaledLattice]
    apply logScaledLattice_inverse_bound
    intro i
    simp only [Pi.neg_apply,neg_neg]
    exact (le_abs_self _).trans (hU x.1 (subset_closure x.2) i)
  have HM : StronglyMeasurable (fun p : S × ℝ => normalizedThetaTail (F p.1) p.2) :=
    normalizedThetaTail_joint_stronglyMeasurable (B := F)
      (fun z => logScaledLattice_measurable_apply B u hu (euclideanInteger z))
  have HN : StronglyMeasurable (fun p : S × ℝ =>
      normalizedThetaTail (adjointEquiv (F p.1).symm) p.2) := by
    have HE : (fun x => adjointEquiv (F x).symm) =
        fun x => logScaledLattice (adjointEquiv B.symm) (-u x) := by
      funext x
      exact adjointEquiv_logScaledLattice B (u x)
    simp_rw [show ∀ x, adjointEquiv (F x).symm =
      logScaledLattice (adjointEquiv B.symm) (-u x) from congrFun HE]
    exact normalizedThetaTail_joint_stronglyMeasurable
      (B := fun x => logScaledLattice (adjointEquiv B.symm) (-u x))
      (fun z => logScaledLattice_measurable_apply _ _ (fun i => (hu i).neg) (euclideanInteger z))
  have HC : ∀ x, ((|(LinearMap.det (F x).toLinearMap)⁻¹|:ℝ):ℂ) =
      ((|(embeddingMatrix M σ).det⁻¹|:ℝ):ℂ) := by
    intro x
    dsimp only [F,u]
    rw [logScaledLattice_det,restoredLogCoordinates_sum,Real.exp_zero,one_mul,
      show LinearMap.det B.toLinearMap = (embeddingMatrix M σ).det from
        fullLatticeEuclideanBasis_det M σ hn]
  have H := averagedThetaMellinXi_differentiable μ F R T hR hT HB HD HM HN _ HC
  have HE : (fun s => ∫ x, thetaMellinXi (F x) s ∂μ) =
      fun s => ∫ u in S, thetaMellinXi (logScaledLattice B (restoredLogCoordinates u)) s := by
    funext s
    exact integral_subtype_comap hS (fun u => thetaMellinXi (logScaledLattice B (restoredLogCoordinates u)) s)
  rw [HE] at H
  exact H

end PrimeDegreePackets

open MeasureTheory Module WithLp
namespace PrimeDegreePackets
open ThetaConstruction

 

theorem arithmeticFlowThetaXi_unitAverage_entire {d : ℕ} {K : Type*}
    [Field K] [NumberField K] [NumberField.IsTotallyReal K] (M : FullLattice (d+1) K)
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1) :
    Differentiable ℂ (fun s => ∫ u in orderedThetaLogDomain σ,
      thetaMellinXi (logScaledLattice (fullLatticeEuclideanBasis M σ hn)
        (restoredLogCoordinates u)) s) :=
  arithmeticFlowThetaXi_boundedAverage_entire M σ hn
    (ZSpan.fundamentalDomain_measurableSet _) (ZSpan.fundamentalDomain_isBounded _)



end PrimeDegreePackets

open scoped BigOperators NumberField nonZeroDivisors ENNReal
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_IdealThetaXi
attribute [-instance] _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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
open scoped ENNReal BigOperators Topology
open MeasureTheory Set Module
open scoped BigOperators ENNReal NumberField nonZeroDivisors
open scoped BigOperators ENNReal NumberField nonZeroDivisors Topology
namespace PrimeDegreePackets.HeckeMellin
open ThetaConstruction


lemma idealThetaXi_entire {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Differentiable ℂ (idealThetaXi σ hn I) := by
  exact (arithmeticFlowThetaXi_unitAverage_entire
    (fractionalIdealFullLattice hn I) σ hn).comp (by fun_prop)

end PrimeDegreePackets.HeckeMellin


namespace PrimeDegreePackets.HeckeMellin
open ThetaConstruction

lemma classThetaXi_entire {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1) : Differentiable ℂ (classThetaXi σ hn) := by
  unfold classThetaXi
  apply Differentiable.fun_sum
  intro c _
  apply Differentiable.mul _ (idealThetaXi_entire σ hn _)
  apply Differentiable.const_cpow differentiable_id
  exact Or.inl (Complex.ofReal_ne_zero.mpr (ne_of_gt (fractionalIdeal_absNorm_pos _)))

end PrimeDegreePackets.HeckeMellin

open Set
namespace PrimeDegreePackets.HeckeMellin



lemma halfPlane_eq_of_real_eq {f g : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f {s | 1 < s.re})
    (hg : DifferentiableOn ℂ g {s | 1 < s.re})
    (hreal : ∀ s : ℝ, 1 < s → f s = g s) :
    EqOn f g {s | 1 < s.re} := by
  have hopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hconn : IsPreconnected {s : ℂ | 1 < s.re} :=
    ((convex_Ioi (1 : ℝ)).linear_preimage Complex.reCLM.toLinearMap).isPreconnected
  have him : Complex.ofReal '' Ioi (2 : ℝ) ⊆ {s : ℂ | f s = g s} \ {(2 : ℂ)} := by
    rintro z ⟨x, hx, rfl⟩
    have hx' : (2 : ℝ) < x := hx
    refine ⟨hreal x (lt_trans (by norm_num) hx'), ?_⟩
    simp only [mem_singleton_iff]
    intro H
    have HR := congrArg Complex.re H
    norm_num at HR
    linarith
  have hcl : (2 : ℂ) ∈ closure (Complex.ofReal '' Ioi (2 : ℝ)) := by
    have H : (2 : ℝ) ∈ closure (Ioi (2 : ℝ)) := by simp [closure_Ioi]
    simpa only [Complex.ofReal_ofNat] using mem_closure_image Complex.continuous_ofReal.continuousAt H
  exact (hf.analyticOnNhd hopen).eqOn_of_preconnected_of_mem_closure
    (hg.analyticOnNhd hopen) hconn (by norm_num) (closure_mono him hcl)

end PrimeDegreePackets.HeckeMellin


namespace PrimeDegreePackets.HeckeMellin
open ThetaConstruction

lemma completedThetaXi_entire {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1) : Differentiable ℂ (completedThetaXi σ hn) := by
  unfold completedThetaXi
  exact (Differentiable.const_mul (by fun_prop) _).mul (classThetaXi_entire σ hn)

end PrimeDegreePackets.HeckeMellin

open Filter Set Module MeasureTheory
open scoped Topology NumberField

open Filter Set Module MeasureTheory WithLp
open scoped Topology NumberField BigOperators nonZeroDivisors
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Arithmetic_ArtinOrders
attribute [-instance] _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Continuing finite Euler-product identities to zero orders

The cyclic permutation identity is first applied to Euler products in
the half-plane of absolute convergence. After clearing the pole at one,
the factors are entire. The identity theorem then gives the corresponding
integer relation among their zero orders everywhere.
-/

open scoped BigOperators Topology
open Filter Set

namespace DukePrimeDegree

open PrimeDegreePackets.HeckeMellin

/-- The actual Dedekind and Hecke continuations are analytic away from
zero and one. Equality on their Dirichlet-series ray determines them on
that connected domain, without choosing pole-clearing factors. -/
theorem analytic_off_zero_one_eq_of_real_eq
    {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f ({0, 1} : Set ℂ)ᶜ)
    (hg : AnalyticOnNhd ℂ g ({0, 1} : Set ℂ)ᶜ)
    (heq : ∀ s : ℝ, 1 < s → f s = g s) :
    EqOn f g ({0, 1} : Set ℂ)ᶜ := by
  have hmem {z : ℂ} (hz : 1 < z.re) : z ∈ ({0, 1} : Set ℂ)ᶜ := by
    simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
    constructor <;> intro h <;> subst z <;> norm_num at hz
  have hhalf := halfPlane_eq_of_real_eq
    (fun z hz => (hf z (hmem hz)).differentiableAt.differentiableWithinAt)
    (fun z hz => (hg z (hmem hz)).differentiableAt.differentiableWithinAt) heq
  apply hf.eqOn_of_preconnected_of_eventuallyEq hg
    (Set.Countable.isConnected_compl_of_one_lt_rank (by simp)
      (by simp : ({0, 1} : Set ℂ).Countable)).2 (z₀ := 2) (by norm_num)
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
    (show 1 < (2 : ℂ).re by norm_num)] with z hz
  exact hhalf hz

/-- A Dirichlet-series product identity gives its zero-order relation
at every point away from the possible poles at zero and one. -/
theorem product_orders_eq_off_zero_one
    {I : Type*} [Fintype I]
    (f : I → ℂ → ℂ)
    (hf : ∀ i, AnalyticOnNhd ℂ (f i) ({0, 1} : Set ℂ)ᶜ)
    (p q : I → ℕ)
    (heq : ∀ s : ℝ, 1 < s → (∏ i, f i s ^ p i) = ∏ i, f i s ^ q i)
    (β : ℂ) (hβ0 : β ≠ 0) (hβ1 : β ≠ 1) :
    (∑ i, (p i : WithTop ℤ) * meromorphicOrderAt (f i) β) =
      ∑ i, (q i : WithTop ℤ) * meromorphicOrderAt (f i) β := by
  classical
  have hβ : β ∈ ({0, 1} : Set ℂ)ᶜ := by simp [hβ0, hβ1]
  have hp : AnalyticOnNhd ℂ (fun z => ∏ i, f i z ^ p i) ({0, 1} : Set ℂ)ᶜ := by
    intro z hz
    exact Finset.analyticAt_fun_prod Finset.univ (fun i _ => (hf i z hz).pow (p i))
  have hq : AnalyticOnNhd ℂ (fun z => ∏ i, f i z ^ q i) ({0, 1} : Set ℂ)ᶜ := by
    intro z hz
    exact Finset.analyticAt_fun_prod Finset.univ (fun i _ => (hf i z hz).pow (q i))
  have he := analytic_off_zero_one_eq_of_real_eq hp hq heq
  have hopen : IsOpen ({0, 1} : Set ℂ)ᶜ :=
    (Set.Finite.isClosed (by simp)).isOpen_compl
  have hv : (fun z => ∏ i, f i z ^ p i) =ᶠ[𝓝[≠] β]
      (fun z => ∏ i, f i z ^ q i) := by
    have hn : ∀ᶠ z in 𝓝 β, z ∈ ({0, 1} : Set ℂ)ᶜ := hopen.mem_nhds hβ
    filter_upwards [hn.filter_mono nhdsWithin_le_nhds] with z hz
    exact he hz
  have H := meromorphicOrderAt_congr hv
  rw [meromorphicOrderAt_fun_prod (s := Finset.univ)
    (f := fun i z => f i z ^ p i)
    (fun i _ => (hf i β hβ).meromorphicAt.pow (p i)),
    meromorphicOrderAt_fun_prod (s := Finset.univ)
    (f := fun i z => f i z ^ q i)
    (fun i _ => (hf i β hβ).meromorphicAt.pow (q i))] at H
  change (∑ i, meromorphicOrderAt (f i ^ p i) β) =
    ∑ i, meromorphicOrderAt (f i ^ q i) β at H
  simpa only [meromorphicOrderAt_pow (hf _ β hβ).meromorphicAt] using H

end DukePrimeDegree

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Arithmetic_CyclicInduction
attribute [-instance] _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Cyclic subgroup coefficients for Stark descent

Möbius inversion on the finite poset of cyclic subgroups expresses the
constant function as an integer combination of their indicators.
Averaging conjugates gives the denominator-cleared cyclic permutation
identity used to compare Dedekind zeta orders.
-/

open scoped BigOperators Classical

namespace DukePrimeDegree

private theorem finite_poset_upper_weights {α : Type*} [PartialOrder α]
    [Fintype α] : ∃ a : α → ℤ, ∀ C,
      (∑ D, if C ≤ D then a D else 0) = 1 := by
  classical
  let : LocallyFiniteOrder (WithTop α) := Fintype.toLocallyFiniteOrder
  let a : α → ℤ := fun C => -IncidenceAlgebra.mu ℤ (C : WithTop α) ⊤
  refine ⟨a, fun C => ?_⟩
  have h := IncidenceAlgebra.sum_Icc_mu_left (𝕜 := ℤ) (C : WithTop α) ⊤
  have hs : (∑ D : WithTop α,
      if (C : WithTop α) ≤ D then IncidenceAlgebra.mu ℤ D ⊤ else 0) = 0 := by
    rw [← Finset.sum_filter]
    have he : Finset.univ.filter (fun D : WithTop α => (C : WithTop α) ≤ D) =
        Finset.Icc (C : WithTop α) ⊤ := by
      ext D
      simp
    rw [he]
    simpa using h
  have hu : (Finset.univ : Finset (WithTop α)) =
      insert ⊤ (Finset.univ.image (fun D : α => (D : WithTop α))) := by
    ext D
    cases D using WithTop.recTopCoe <;> simp
  rw [hu, Finset.sum_insert (by simp),
    Finset.sum_image (fun _ _ _ _ h => WithTop.coe_injective h)] at hs
  simp only [show (C : WithTop α) ≤ ⊤ from le_top, ite_true, if_true,
    IncidenceAlgebra.mu_self, WithTop.coe_le_coe] at hs
  have he : (∑ D : α, if C ≤ D then a D else 0) =
      -(∑ D : α, if C ≤ D then IncidenceAlgebra.mu ℤ (D : WithTop α) ⊤ else 0) := by
    simp only [a, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro D _
    split_ifs <;> simp
  rw [he]
  linarith

/-- Integer cyclic-subgroup indicator coefficients. -/
theorem exists_cyclic_indicator_coefficients
    (G : Type*) [Group G] [Finite G] :
    ∃ a : CyclicSubgroups G → ℤ, ∀ g : G,
      (∑ C, if g ∈ C.val then a C else 0) = 1 := by
  classical
  obtain ⟨a, ha⟩ := finite_poset_upper_weights (α := CyclicSubgroups G)
  refine ⟨a, fun g => ?_⟩
  let C : CyclicSubgroups G := ⟨Subgroup.zpowers g, inferInstance⟩
  convert ha C using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.sum_congr rfl
  intro D _
  have he : C ≤ D ↔ g ∈ D.val := by
    change Subgroup.zpowers g ≤ D.val ↔ g ∈ D.val
    exact Subgroup.zpowers_le
  simp only [he]

/-- The permutation character counts fixed points in the actual coset
representation used by the Artin Euler factors. -/
theorem permutation_character_eq_fixed_sum
    {G Ω : Type*} [Monoid G] [Fintype Ω] [MulAction G Ω] (g : G) :
    (Representation.ofMulAction ℂ G Ω).character g =
      ∑ x : Ω, if g • x = x then (1 : ℂ) else 0 := by
  classical
  let b : Module.Basis Ω ℂ (MonoidAlgebra ℂ Ω) :=
    Finsupp.basisSingleOne.map (MonoidAlgebra.coeffLinearEquiv ℂ).symm
  rw [Representation.character, LinearMap.trace_eq_matrix_trace ℂ b]
  simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply]
  apply Finset.sum_congr rfl
  intro x _
  simp [b, Finsupp.single_apply, eq_comm]

/-- Conjugacy counting and the coset permutation character differ by
exactly the subgroup order. -/
theorem conjugacy_indicator_sum_eq_card_mul_character
    {G : Type*} [Group G] [Fintype G] (H : Subgroup G) (g : G) :
    (∑ x : G, if x⁻¹ * g * x ∈ H then (1 : ℂ) else 0) =
      Fintype.card H * (Representation.ofMulAction ℂ G (G ⧸ H)).character g := by
  classical
  let e := Subgroup.groupEquivQuotientProdSubgroup (s := H)
  have he (x : G) : (e x).1 = QuotientGroup.mk x := rfl
  have hf (x : G) : g • (QuotientGroup.mk x : G ⧸ H) = QuotientGroup.mk x ↔
      x⁻¹ * g * x ∈ H := by
    change QuotientGroup.mk (g * x) = QuotientGroup.mk x ↔ _
    rw [eq_comm, QuotientGroup.eq]
    simp only [mul_assoc]
  calc
    _ = ∑ p : (G ⧸ H) × H, if g • p.1 = p.1 then (1 : ℂ) else 0 := by
      apply Fintype.sum_equiv e
      intro x
      simp only [he, hf]
    _ = Fintype.card H * ∑ q : G ⧸ H, if g • q = q then (1 : ℂ) else 0 := by
      rw [Fintype.sum_prod_type]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      by_cases hq : g • q = q <;> simp [hq]
    _ = _ := by
      rw [permutation_character_eq_fixed_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro q _
      by_cases hq : g • q = q <;> simp only [hq, ite_true, if_true, ite_false, if_false]

end DukePrimeDegree

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_SubgroupInduction
attribute [-instance] _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Cyclic induction inside an arbitrary subgroup

The permutation character of `G/H` is an integer combination, after
multiplication by `card H`, of the permutation characters for cyclic
subgroups contained in `H`. This is the form needed for the Dedekind
zeta function of a possibly nonnormal intermediate field.
-/

open scoped BigOperators Classical

namespace DukePrimeDegree

theorem cyclic_indicator_inside_subgroup
    {G : Type*} [Group G] [Fintype G] (H : Subgroup G)
    (a : CyclicSubgroups H → ℤ)
    (ha : ∀ h : H, (∑ C, if h ∈ C.val then a C else 0) = 1)
    (g : G) :
    (∑ C : CyclicSubgroups H, if g ∈ C.val.map H.subtype then a C else 0) =
      if g ∈ H then 1 else 0 := by
  by_cases hg : g ∈ H
  · let h : H := ⟨g, hg⟩
    have hm (C : CyclicSubgroups H) : g ∈ C.val.map H.subtype ↔ h ∈ C.val := by
      change H.subtype h ∈ C.val.map H.subtype ↔ h ∈ C.val
      exact Subgroup.mem_map_iff_mem H.subtype_injective
    simpa only [hm, ite_eq_left hg] using ha h
  · have hm (C : CyclicSubgroups H) : g ∉ C.val.map H.subtype := by
      rintro ⟨h, _, he⟩
      exact hg (he ▸ h.property)
    simp [hm, hg]

theorem cyclic_permutation_character_identity_inside
    {G : Type*} [Group G] [Fintype G] (H : Subgroup G)
    (a : CyclicSubgroups H → ℤ)
    (ha : ∀ h : H, (∑ C, if h ∈ C.val then a C else 0) = 1) :
    ∀ g : G,
      (∑ C, ((a C * Fintype.card (C.val.map H.subtype) : ℤ) : ℂ) *
        (Representation.ofMulAction ℂ G (G ⧸ C.val.map H.subtype)).character g) =
      Fintype.card H * (Representation.ofMulAction ℂ G (G ⧸ H)).character g := by
  intro g
  have hs (x : G) : (∑ C : CyclicSubgroups H, (a C : ℂ) *
      (if x⁻¹ * g * x ∈ C.val.map H.subtype then (1 : ℂ) else 0)) =
      if x⁻¹ * g * x ∈ H then 1 else 0 := by
    have he := cyclic_indicator_inside_subgroup H a ha (x⁻¹ * g * x)
    have he' : (∑ C : CyclicSubgroups H,
        if x⁻¹ * g * x ∈ C.val.map H.subtype then (a C : ℂ) else 0) =
        if x⁻¹ * g * x ∈ H then (1 : ℂ) else 0 := by
      exact_mod_cast he
    simpa only [mul_ite, mul_one, mul_zero] using he'
  calc
    _ = ∑ C : CyclicSubgroups H, (a C : ℂ) *
        ∑ x : G, if x⁻¹ * g * x ∈ C.val.map H.subtype then (1 : ℂ) else 0 := by
      apply Finset.sum_congr rfl
      intro C _
      rw [Int.cast_mul, Int.cast_natCast, conjugacy_indicator_sum_eq_card_mul_character]
      ring
    _ = ∑ x : G, ∑ C : CyclicSubgroups H, (a C : ℂ) *
        (if x⁻¹ * g * x ∈ C.val.map H.subtype then (1 : ℂ) else 0) := by
      simp only [Finset.mul_sum]
      exact Finset.sum_comm
    _ = ∑ x : G, if x⁻¹ * g * x ∈ H then (1 : ℂ) else 0 := by
      simp only [hs]
    _ = _ := conjugacy_indicator_sum_eq_card_mul_character H g

end DukePrimeDegree

end OAI
end

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
-- module Solutions.OAIQ244_DUKE.PrimePackets_RealMellin
attribute [-instance] _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EmbeddingOrder.toRealOrder_apply
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

lemma regularizedThetaZeta_eq_totallyReal {d : ℕ} {K : Type*}
    [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
     {s : ℂ} (hs : 1 < s.re) :
    regularizedThetaZeta σ hn s = (s-1)*NumberField.dedekindZeta K s := by
  unfold regularizedThetaZeta
  rw [completedThetaXi_eq_totallyReal σ hn  hs]
  have hE := completionExponential_ne_zero (d+1) |(NumberField.discr K : ℝ)| s
  have hG := Complex.Gamma_ne_zero (half_ne_nonpositive_integer (by linarith : 0 < s.re))
  have hs0 := Complex.ne_zero_of_one_lt_re hs
  unfold totallyRealCompletedXi
  rw [hn]
  rw [inv_pow]
  field_simp [hE, hG, hs0]

end PrimeDegreePackets.HeckeMellin


end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_FunctionalEquation
attribute [-instance] _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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

end PrimeDegreePackets.HeckeMellin


open IntermediateField Module

open Module IntermediateField
open scoped BigOperators NumberField Pointwise
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
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_FiniteOrderSpectrum
attribute [-instance] _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Spectral data for finite-order Artin operators

The local permutation and monomial operators have finite order. Their
eigenbases express both traces and Euler determinants using the same
finite list of eigenvalues.
-/

noncomputable section
open Module
open scoped BigOperators Classical Polynomial

namespace DukePrimeDegree

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

theorem exists_eigenbasis_of_finite_order (T : Module.End ℂ V)
    {m : ℕ} (hm : 0 < m) (hT : T ^ m = 1) :
    ∃ (n : ℕ) (b : Basis (Fin n) ℂ V) (lam : Fin n → ℂ),
      ∀ i, T (b i) = lam i • b i := by
  have hss : T.IsSemisimple := by
    apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero
      (p := Polynomial.X ^ m - 1)
    · exact (Polynomial.X_pow_sub_one_separable_iff.mpr
        (by exact_mod_cast hm.ne' : (m : ℂ) ≠ 0)).squarefree
    · simpa using sub_eq_zero.mpr hT
  have hi : DirectSum.IsInternal T.eigenspace :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
      T.eigenspaces_iSupIndep hss.iSup_eigenspace_eq_top
  have hi' : DirectSum.IsInternal (fun μ : T.Eigenvalues => T.eigenspace μ.val) :=
    (DirectSum.isInternal_ne_bot_iff).mpr hi
  let b := hi'.collectedBasis (fun μ => Module.finBasis ℂ (T.eigenspace μ.val))
  let I := (μ : T.Eigenvalues) × Fin (finrank ℂ (T.eigenspace μ.val))
  let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  refine ⟨Fintype.card I, b.reindex e, fun i => (e.symm i).1.val, ?_⟩
  intro i
  apply Module.End.mem_eigenspace_iff.mp
  simpa only [Basis.reindex_apply, b] using
    hi'.collectedBasis_mem (fun μ => Module.finBasis ℂ (T.eigenspace μ.val)) (e.symm i)

omit [FiniteDimensional ℂ V] in
theorem trace_eq_sum_of_eigenbasis {ι : Type*} [Fintype ι]
    (b : Basis ι ℂ V) (T : Module.End ℂ V) (lam : ι → ℂ)
    (hT : ∀ i, T (b i) = lam i • b i) :
    LinearMap.trace ℂ V T = ∑ i, lam i := by
  rw [LinearMap.trace_eq_matrix_trace ℂ b]
  have he : LinearMap.toMatrix b b T = Matrix.diagonal lam := by
    ext i j
    rw [LinearMap.toMatrix_apply', hT j, map_smul]
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij]
  rw [he, Matrix.trace_diagonal]

omit [FiniteDimensional ℂ V] in
theorem trace_pow_eq_sum_of_eigenbasis {ι : Type*} [Fintype ι]
    (b : Basis ι ℂ V) (T : Module.End ℂ V) (lam : ι → ℂ)
    (hT : ∀ i, T (b i) = lam i • b i) (k : ℕ) :
    LinearMap.trace ℂ V (T ^ k) = ∑ i, lam i ^ k := by
  apply trace_eq_sum_of_eigenbasis b
  intro i
  exact (show T.HasEigenvector (lam i) (b i) from
    ⟨Module.End.mem_eigenspace_iff.mpr (hT i), b.ne_zero i⟩).pow_apply k

omit [FiniteDimensional ℂ V] in
theorem euler_det_eq_prod_of_eigenbasis {ι : Type*} [Fintype ι]
    (b : Basis ι ℂ V) (T : Module.End ℂ V) (lam : ι → ℂ)
    (hT : ∀ i, T (b i) = lam i • b i) (z : ℂ) :
    (LinearMap.id - z • T).det = ∏ i, (1 - z * lam i) := by
  apply PrimeDegreePackets.GaloisIdealCharacter.det_eq_prod_of_eigenbasis b
  intro i
  simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smul_apply,
    hT, smul_smul, sub_smul, one_smul]

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_SpectralMoments
attribute [-instance] _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Power traces determine finite Euler products

Finite spectra are determined by all their power sums. This is the
linear-algebra step that turns the cyclic character identities into
identities of local Artin Euler factors.
-/

noncomputable section
open Module
open scoped BigOperators Classical

namespace DukePrimeDegree

theorem finite_weights_eq_zero_of_moments
    {I : Type*} [Fintype I] (lam a : I → ℂ) (hlam : Function.Injective lam)
    (h : ∀ k : ℕ, (∑ i, a i * lam i ^ k) = 0) : a = 0 := by
  let e := Fintype.equivFin I
  have he : Function.Injective (fun i => lam (e.symm i)) := hlam.comp e.symm.injective
  have hm : ∀ k : Fin (Fintype.card I),
      (∑ i : Fin (Fintype.card I), a (e.symm i) * lam (e.symm i) ^ (k : ℕ)) = 0 := by
    intro k
    exact (Fintype.sum_equiv e.symm _ _ (fun _ => rfl)).trans (h k)
  have hz := Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero he hm
  funext i
  simpa using congrFun hz (e i)

theorem weighted_euler_products_eq_of_moments
    {I : Type*} [Fintype I] (lam : I → ℂ) (p q : I → ℕ)
    (h : ∀ k : ℕ, (∑ i, (p i : ℂ) * lam i ^ k) =
      ∑ i, (q i : ℂ) * lam i ^ k) (z : ℂ) :
    (∏ i, (1 - z * lam i) ^ p i) = ∏ i, (1 - z * lam i) ^ q i := by
  let J := Set.range lam
  let : Fintype J := (Set.finite_range lam).fintype
  let r : I → J := fun i => ⟨lam i, ⟨i, rfl⟩⟩
  let weight (t : I → ℕ) (j : J) := ∑ i ∈ Finset.univ.filter (fun i => r i = j), t i
  have regroup (t : I → ℕ) (k : ℕ) :
      (∑ j : J, (weight t j : ℂ) * j.val ^ k) = ∑ i, (t i : ℂ) * lam i ^ k := by
    calc
      _ = ∑ j : J, ∑ i ∈ Finset.univ.filter (fun i => r i = j),
          (t i : ℂ) * lam i ^ k := by
        apply Finset.sum_congr rfl
        intro j _
        simp only [weight, Nat.cast_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i hi
        have hij : lam i = j.val := congrArg Subtype.val (Finset.mem_filter.mp hi).2
        rw [hij]
      _ = _ := Finset.sum_fiberwise Finset.univ r _
  have hw : (fun j : J => (weight p j : ℂ) - (weight q j : ℂ)) = 0 := by
    apply finite_weights_eq_zero_of_moments Subtype.val _ Subtype.val_injective
    intro k
    simp only [sub_mul, Finset.sum_sub_distrib]
    rw [regroup, regroup, h, sub_self]
  have hweight (j : J) : weight p j = weight q j := by
    have he := congrFun hw j
    simp only [Pi.zero_apply, sub_eq_zero] at he
    exact_mod_cast he
  have prod_regroup (t : I → ℕ) :
      (∏ i, (1 - z * lam i) ^ t i) =
        ∏ j : J, (1 - z * j.val) ^ weight t j := by
    calc
      _ = ∏ j : J, ∏ i ∈ Finset.univ.filter (fun i => r i = j),
          (1 - z * lam i) ^ t i :=
        (Finset.prod_fiberwise Finset.univ r _).symm
      _ = _ := by
        apply Finset.prod_congr rfl
        intro j _
        dsimp only [weight]
        rw [← Finset.prod_pow_eq_pow_sum]
        apply Finset.prod_congr rfl
        intro i hi
        have hij : lam i = j.val := congrArg Subtype.val (Finset.mem_filter.mp hi).2
        rw [hij]
  rw [prod_regroup, prod_regroup]
  simp only [hweight]

/-- Equality of finite-group characters gives the corresponding local
Euler-factor identity. The natural exponents permit denominator-cleared
integer character relations. -/
theorem euler_det_products_eq_of_characters
    {I G : Type*} [Fintype I] [Group G] [Finite G]
    {V : I → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    [∀ i, FiniteDimensional ℂ (V i)]
    (ρ : ∀ i, Representation ℂ G (V i)) (p q : I → ℕ)
    (h : ∀ g, (∑ i, (p i : ℂ) * (ρ i).character g) =
      ∑ i, (q i : ℂ) * (ρ i).character g)
    (g : G) (z : ℂ) :
    (∏ i, (LinearMap.id - z • ρ i g).det ^ p i) =
      ∏ i, (LinearMap.id - z • ρ i g).det ^ q i := by
  have hb (i : I) : ∃ (n : ℕ) (b : Basis (Fin n) ℂ (V i)) (lam : Fin n → ℂ),
      ∀ j, ρ i g (b j) = lam j • b j := by
    apply exists_eigenbasis_of_finite_order (ρ i g) (Nat.card_pos (α := G))
    rw [← map_pow, pow_card_eq_one', map_one]
  choose n b lam hb using hb
  let μ : (i : I) × Fin (n i) → ℂ := fun j => lam j.1 j.2
  have hm : ∀ k : ℕ,
      (∑ j : (i : I) × Fin (n i), (p j.1 : ℂ) * μ j ^ k) =
        ∑ j : (i : I) × Fin (n i), (q j.1 : ℂ) * μ j ^ k := by
    intro k
    have he (i : I) : (ρ i).character (g ^ k) = ∑ j, lam i j ^ k := by
      rw [Representation.character, map_pow]
      exact trace_pow_eq_sum_of_eigenbasis (b i) (ρ i g) (lam i) (hb i) k
    simpa only [Fintype.sum_sigma, μ, ← Finset.mul_sum, he] using h (g ^ k)
  have H := weighted_euler_products_eq_of_moments μ
    (fun j => p j.1) (fun j => q j.1) hm z
  simp only [Fintype.prod_sigma, μ, Finset.prod_pow] at H
  simpa only [← euler_det_eq_prod_of_eigenbasis (b _) (ρ _ g) (lam _) (hb _) z] using H

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Arithmetic_PermutationEuler
attribute [-instance] _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Permutation characters and local Euler determinants

The permutation representation on the group algebra and the translation
operator on functions have conjugate matrices. This connects the cyclic
induction identities to the actual Frobenius Euler determinants.
-/

noncomputable section
open scoped BigOperators Classical

namespace DukePrimeDegree

theorem permutationFunctionEquiv_translate
    {G X : Type*} [Group G] [MulAction G X] [Finite X]
    (g : G) (f : MonoidAlgebra ℂ X) :
    permutationFunctionEquiv X (Representation.ofMulAction ℂ G X g f) =
      LinearEquiv.funCongrLeft ℂ ℂ (MulAction.toPerm g⁻¹)
        (permutationFunctionEquiv X f) := by
  funext x
  exact Representation.coeff_ofMulAction g f x

theorem permutation_euler_det_eq
    {G X : Type*} [Group G] [MulAction G X] [Finite X]
    (g : G) (z : ℂ) :
    (LinearMap.id - z • Representation.ofMulAction ℂ G X g).det =
      (LinearMap.id - z •
        (LinearEquiv.funCongrLeft ℂ ℂ (MulAction.toPerm (β := X) g⁻¹)).toLinearMap).det := by
  let e := permutationFunctionEquiv X
  rw [← LinearMap.det_conj (LinearMap.id - z • Representation.ofMulAction ℂ G X g) e]
  congr 1
  apply LinearMap.ext
  intro f
  funext x
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply,
    LinearMap.smul_apply, LinearEquiv.coe_coe, map_sub, map_smul,
    LinearEquiv.apply_symm_apply]
  rw [show e (Representation.ofMulAction ℂ G X g (e.symm f)) =
    LinearEquiv.funCongrLeft ℂ ℂ (MulAction.toPerm g⁻¹) (e (e.symm f)) from
      permutationFunctionEquiv_translate g (e.symm f)]
  rw [LinearEquiv.apply_symm_apply]

end DukePrimeDegree

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
-- module Solutions.OAIQ244_DUKE.PrimePackets_CosetMeromorphic
attribute [-instance] _root_.AlgebraicNumberTheory.numberFieldInRationalSeparableClosure_numberField _root_.HilbertRamification.Dedekind.basePrime_isPrime _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.finiteNormalClosure_numberField _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EmbeddingOrder.toRealOrder_apply
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

lemma removedEulerPolynomial_entire (N : ℕ) :
    Differentiable ℂ (removedEulerPolynomial K N) := by
  apply Differentiable.fun_finsetProd
  intro p _
  apply Differentiable.fun_finsetProd
  intro P _
  have hn : (Ideal.absNorm P.val : ℂ) ≠ 0 := by
    exact_mod_cast (by have := idealsOverPrime_norm_two_le K P.property; omega :
      Ideal.absNorm P.val ≠ 0)
  exact (differentiable_const (1 : ℂ)).sub (differentiable_id.neg.const_cpow (Or.inl hn))

lemma removedEulerPolynomial_ne_zero (N : ℕ) {s : ℂ} (hs : 0 < s.re) :
    removedEulerPolynomial K N s ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro p _
  apply Finset.prod_ne_zero_iff.mpr
  intro P _
  exact primeEuler_denominator_ne_zero K P hs

end EulerCorrection

lemma cosetRationalEuler_hasProd (L : IntermediateField F E) (N : ℕ) (hN : 0 < N)
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
section ContinuedCoset
variable {d : ℕ} {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]



lemma gammaInverse_entire :
    Differentiable ℂ (fun s : ℂ => (Complex.Gamma (s/2))⁻¹) := by
  simpa only [one_div, Function.comp_def, id_eq] using
    (Complex.differentiable_one_div_Gamma.comp (differentiable_id.div_const 2))

omit [NumberField.IsTotallyReal K] in
lemma exponentialInverse_entire : Differentiable ℂ
    (fun s : ℂ => (completionExponential (d+1) |(NumberField.discr K : ℝ)| s)⁻¹) := by
  have HE : Differentiable ℂ (completionExponential (d+1) |(NumberField.discr K : ℝ)|) :=
    fun s => (completionExponential_hasDerivAt _ _ s).differentiableAt
  exact HE.inv (fun s => completionExponential_ne_zero _ _ s)

omit [NumberField.IsTotallyReal K] in
lemma cosetXiFactor_meromorphicAt (N : ℕ) (s : ℂ) :
    MeromorphicAt (cosetXiFactor (K := K) (d := d) N) s := by
  have hA := (((removedEulerPolynomial_entire K N).analyticAt s).mul
    ((exponentialInverse_entire (K := K) (d := d)).analyticAt s)).mul
    ((gammaInverse_entire.analyticAt s).pow (d+1))
  exact (hA.meromorphicAt.div analyticAt_id.meromorphicAt).div
    (analyticAt_id.sub analyticAt_const).meromorphicAt

omit [NumberField.IsTotallyReal K] in
lemma cosetXiFactor_analyticAt (N : ℕ) {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    AnalyticAt ℂ (cosetXiFactor (K := K) (d := d) N) s := by
  have hA := (((removedEulerPolynomial_entire K N).analyticAt s).mul
    ((exponentialInverse_entire (K := K) (d := d)).analyticAt s)).mul
    ((gammaInverse_entire.analyticAt s).pow (d+1))
  exact (hA.div analyticAt_id hs0).div (analyticAt_id.sub analyticAt_const)
    (sub_ne_zero.mpr hs1)

omit [NumberField.IsTotallyReal K] in
lemma cosetXiFactor_ne_zero (N : ℕ) {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    cosetXiFactor (K := K) (d := d) N s ≠ 0 := by
  apply div_ne_zero _ (sub_ne_zero.mpr hs1)
  apply div_ne_zero _ (by contrapose! hs; simp [hs])
  apply mul_ne_zero
  · exact mul_ne_zero (removedEulerPolynomial_ne_zero K N hs)
      (inv_ne_zero (completionExponential_ne_zero _ _ s))
  · exact pow_ne_zero _ (inv_ne_zero (Complex.Gamma_ne_zero (half_ne_nonpositive_integer hs)))

lemma cosetMeromorphic_eq_factor (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1) (N : ℕ) :
    cosetMeromorphic σ hn N = cosetXiFactor (K := K) (d := d) N * completedThetaXi σ hn := by
  funext s
  simp only [cosetMeromorphic, cosetXiFactor, regularizedThetaZeta, Pi.mul_apply,
    div_eq_mul_inv]
  ring

lemma cosetMeromorphic_meromorphicAt (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1) (N : ℕ) (s : ℂ) : MeromorphicAt (cosetMeromorphic σ hn N) s := by
  rw [cosetMeromorphic_eq_factor]
  exact (cosetXiFactor_meromorphicAt N s).mul
    ((completedThetaXi_entire σ hn).analyticAt s).meromorphicAt

lemma cosetMeromorphic_eq_dedekindZeta (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1) (N : ℕ) {s : ℂ} (hs : 1 < s.re) :
    cosetMeromorphic σ hn N s = NumberField.dedekindZeta K s * removedEulerPolynomial K N s := by
  have hs1 : s - 1 ≠ 0 := by
    apply sub_ne_zero.mpr
    intro he
    simp [he] at hs
  rw [cosetMeromorphic, regularizedThetaZeta_eq_totallyReal σ hn hs,
    mul_div_cancel_left₀ _ hs1, mul_comm]

 

theorem cosetMeromorphic_order_eq (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1) (N : ℕ) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    meromorphicOrderAt (cosetMeromorphic σ hn N) (β : ℂ) =
      meromorphicOrderAt (completedThetaXi σ hn) (β : ℂ) := by
  have h0 : (β : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hβ0.ne'
  have h1 : (β : ℂ) ≠ 1 := by exact_mod_cast hβ1.ne
  rw [cosetMeromorphic_eq_factor]
  exact meromorphicOrderAt_mul_of_ne_zero (cosetXiFactor_analyticAt N h0 h1)
    (cosetXiFactor_ne_zero N hβ0 h1)

end ContinuedCoset

 

theorem actual_coset_meromorphic_pairing
    (L : IntermediateField F E) [NumberField.IsTotallyReal L] {d : ℕ}
    (σ : OrderedEmbeddings (d+1) L) (hn : finrank ℚ L = d+1)
    (N : ℕ) (hN : 0 < N) (hD : (NumberField.discr E).natAbs ∣ N) :
    (∀ s : ℂ, MeromorphicAt (cosetMeromorphic σ hn N) s) ∧
    (∀ s : ℂ, 1 < s.re → HasProd (fun p : Nat.Primes => cosetRationalEuler F E L N p s)
      (cosetMeromorphic σ hn N s)) ∧
    (∀ β : ℝ, 0 < β → β < 1 →
      meromorphicOrderAt (cosetMeromorphic σ hn N) (β : ℂ) =
        meromorphicOrderAt (completedThetaXi σ hn) (β : ℂ)) := by
  refine ⟨cosetMeromorphic_meromorphicAt σ hn N, ?_, ?_⟩
  · intro s hs
    rw [cosetMeromorphic_eq_dedekindZeta σ hn N hs]
    exact cosetRationalEuler_hasProd F E L N hN hD hs
  · intro β hβ0 hβ1
    exact cosetMeromorphic_order_eq σ hn N hβ0 hβ1

end PrimeDegreePackets.GaloisIdealCharacter

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Arithmetic_ZetaOrder
attribute [-instance] _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A choice-independent continued zeta order

Zero orders do not depend on the ordering of the real embeddings or on
the finite set of removed Euler factors. We fix one ordering only to
package the continued zeta order as a function of a number field.
-/

noncomputable section
open Filter Set Module
open scoped NumberField Classical Topology

namespace DukePrimeDegree

open PrimeDegreePackets PrimeDegreePackets.GaloisIdealCharacter
  PrimeDegreePackets.HeckeMellin

variable {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]

theorem coset_analytic_off_zero_one
    {d : ℕ} (σ : OrderedEmbeddings (d + 1) K) (hn : finrank ℚ K = d + 1)
    (N : ℕ) : AnalyticOnNhd ℂ (cosetMeromorphic σ hn N) ({0, 1} : Set ℂ)ᶜ := by
  intro z hz
  rw [cosetMeromorphic_eq_factor]
  exact (cosetXiFactor_analyticAt N (by simpa using (not_or.mp hz).1)
    (by simpa using (not_or.mp hz).2)).mul
      ((completedThetaXi_entire σ hn).analyticAt z)

theorem coset_order_independent_of_data
    {d e : ℕ} (σ : OrderedEmbeddings (d + 1) K) (hn : finrank ℚ K = d + 1)
    (τ : OrderedEmbeddings (e + 1) K) (he : finrank ℚ K = e + 1)
    (N M : ℕ) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    meromorphicOrderAt (cosetMeromorphic σ hn N) (β : ℂ) =
      meromorphicOrderAt (cosetMeromorphic τ he M) (β : ℂ) := by
  have hanalytic {k : ℕ} (υ : OrderedEmbeddings (k + 1) K)
      (hk : finrank ℚ K = k + 1) (A B : ℕ) :
      AnalyticOnNhd ℂ (removedEulerPolynomial K A * cosetMeromorphic υ hk B)
        ({0, 1} : Set ℂ)ᶜ := by
    intro z hz
    apply ((removedEulerPolynomial_entire K A).analyticAt z).mul
    rw [cosetMeromorphic_eq_factor]
    exact (cosetXiFactor_analyticAt B (by simpa using (not_or.mp hz).1)
      (by simpa using (not_or.mp hz).2)).mul
        ((completedThetaXi_entire υ hk).analyticAt z)
  have heq := analytic_off_zero_one_eq_of_real_eq
    (hanalytic σ hn M N) (hanalytic τ he N M) (fun s hs => by
      simp only [Pi.mul_apply]
      rw [cosetMeromorphic_eq_dedekindZeta σ hn N hs,
        cosetMeromorphic_eq_dedekindZeta τ he M hs]
      ring)
  have hβ : (β : ℂ) ∈ ({0, 1} : Set ℂ)ᶜ := by
    simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
    exact ⟨Complex.ofReal_ne_zero.mpr hβ0.ne', by exact_mod_cast hβ1.ne⟩
  have hopen : IsOpen ({0, 1} : Set ℂ)ᶜ :=
    (Set.Finite.isClosed (by simp)).isOpen_compl
  have hv : removedEulerPolynomial K M * cosetMeromorphic σ hn N =ᶠ[𝓝[≠] (β : ℂ)]
      removedEulerPolynomial K N * cosetMeromorphic τ he M := by
    have hu : ∀ᶠ z in 𝓝 (β : ℂ), z ∈ ({0, 1} : Set ℂ)ᶜ := hopen.mem_nhds hβ
    filter_upwards [hu.filter_mono nhdsWithin_le_nhds] with z hz
    exact heq hz
  have H := meromorphicOrderAt_congr hv
  rw [meromorphicOrderAt_mul_of_ne_zero ((removedEulerPolynomial_entire K M).analyticAt _)
      (removedEulerPolynomial_ne_zero K M hβ0),
    meromorphicOrderAt_mul_of_ne_zero ((removedEulerPolynomial_entire K N).analyticAt _)
      (removedEulerPolynomial_ne_zero K N hβ0)] at H
  exact H

theorem zetaZeroOrder_eq_coset_order
    {d : ℕ} (σ : OrderedEmbeddings (d + 1) K) (hn : finrank ℚ K = d + 1)
    (N : ℕ) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    zetaZeroOrder K β = meromorphicOrderAt (cosetMeromorphic σ hn N) (β : ℂ) :=
  coset_order_independent_of_data _ _ σ hn 1 N hβ0 hβ1

theorem zetaZeroOrder_eq_completed_order
    {d : ℕ} (σ : OrderedEmbeddings (d + 1) K) (hn : finrank ℚ K = d + 1)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    zetaZeroOrder K β = meromorphicOrderAt (completedThetaXi σ hn) (β : ℂ) := by
  rw [zetaZeroOrder_eq_coset_order σ hn 1 hβ0 hβ1,
    cosetMeromorphic_order_eq σ hn 1 hβ0 hβ1]

theorem zetaZeroOrder_finite_nonnegative
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ m : ℕ, zetaZeroOrder K β = (m : WithTop ℤ) := by
  let σ := canonicalRealEmbeddings K
  let hn := degreePred_spec K
  rw [zetaZeroOrder_eq_completed_order σ hn hβ0 hβ1]
  have ha : ∀ z, AnalyticAt ℂ (completedThetaXi σ hn) z :=
    fun z => (completedThetaXi_entire σ hn).analyticAt z
  have hfin : analyticOrderAt (completedThetaXi σ hn) (β : ℂ) ≠ ⊤ := by
    intro H
    have hz := (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero (β : ℂ) ha).mp H
    exact (completedThetaXi_ne_zero_of_re_gt_one_totallyReal σ hn (s := 2)
      (by norm_num)) (congrFun hz 2)
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hfin
  refine ⟨m, ?_⟩
  rw [(ha (β : ℂ)).meromorphicOrderAt_eq, ← hm, ENat.map_natCast]
  rfl

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Arithmetic_ConjugateSubfields
attribute [-instance] _root_.AlgebraicNumberTheory.numberFieldInRationalSeparableClosure_numberField _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueExtension_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.finiteIdeleGroupT2Space _root_.finiteNormalClosure_numberField _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Conjugate subfields have the same zeta zero order

Conjugate subgroups have the same permutation character. The
character-to-Euler identity identifies their actual incomplete Dedekind
zeta functions, and analytic continuation identifies their zero orders.
-/

noncomputable section
open Module Filter Set
open scoped NumberField BigOperators Classical Topology

namespace DukePrimeDegree

open PrimeDegreePackets PrimeDegreePackets.GaloisIdealCharacter
  PrimeDegreePackets.HeckeMellin

theorem permutation_character_conjugate_subgroup
    {G : Type*} [Group G] [Fintype G] (H : Subgroup G) (a g : G) :
    (Representation.ofMulAction ℂ G (G ⧸ H.map (MulAut.conj a).toMonoidHom)).character g =
      (Representation.ofMulAction ℂ G (G ⧸ H)).character g := by
  let H' := H.map (MulAut.conj a).toMonoidHom
  have hcard : Fintype.card H' = Fintype.card H := by
    exact Fintype.card_congr (H.equivMapOfInjective
      (MulAut.conj a).toMonoidHom (MulAut.conj a).injective).toEquiv.symm
  have hsum : (∑ x : G, if x⁻¹ * g * x ∈ H' then (1 : ℂ) else 0) =
      ∑ x : G, if x⁻¹ * g * x ∈ H then (1 : ℂ) else 0 := by
    apply Fintype.sum_equiv (Equiv.mulRight a)
    intro x
    have hmem : x⁻¹ * g * x ∈ H' ↔ (x * a)⁻¹ * g * (x * a) ∈ H := by
      rw [Subgroup.mem_map_equiv]
      simp only [MulAut.conj_symm_apply, mul_inv_rev, mul_assoc]
    change (if x⁻¹ * g * x ∈ H' then (1 : ℂ) else 0) =
      if (x * a)⁻¹ * g * (x * a) ∈ H then 1 else 0
    rw [hmem]
  rw [conjugacy_indicator_sum_eq_card_mul_character,
    conjugacy_indicator_sum_eq_card_mul_character, hcard] at hsum
  exact mul_left_cancel₀ (by exact_mod_cast Fintype.card_ne_zero (α := H)) hsum

theorem permutation_euler_eq_of_character_eq
    {G : Type*} [Group G] [Fintype G] (H J : Subgroup G)
    (hχ : ∀ g, (Representation.ofMulAction ℂ G (G ⧸ H)).character g =
      (Representation.ofMulAction ℂ G (G ⧸ J)).character g)
    (g : G) (z : ℂ) :
    (LinearMap.id - z • Representation.ofMulAction ℂ G (G ⧸ H) g).det =
      (LinearMap.id - z • Representation.ofMulAction ℂ G (G ⧸ J) g).det := by
  let : Fintype (Subgroup G) := Fintype.ofFinite _
  let p : Subgroup G → ℕ := fun S => if S = H then 1 else 0
  let q : Subgroup G → ℕ := fun S => if S = J then 1 else 0
  have h := euler_det_products_eq_of_characters
    (V := fun S : Subgroup G => MonoidAlgebra ℂ (G ⧸ S))
    (fun S => Representation.ofMulAction ℂ G (G ⧸ S)) p q
    (fun g => by simpa [p, q] using hχ g) g z
  simpa [p, q] using h

variable {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E]
variable [Algebra F E] [FiniteDimensional F E] [IsGalois F E]

attribute [local instance] OAI.DukePrimeDegree.instFintypeAlgEquiv_solutions
theorem cosetRationalEuler_eq_of_permutation_characters
    (L M : IntermediateField F E)
    (hχ : ∀ g,
      (Representation.ofMulAction ℂ (E ≃ₐ[F] E) ((E ≃ₐ[F] E) ⧸ L.fixingSubgroup)).character g =
      (Representation.ofMulAction ℂ (E ≃ₐ[F] E) ((E ≃ₐ[F] E) ⧸ M.fixingSubgroup)).character g)
    (N : ℕ) (p : Nat.Primes) (s : ℂ) :
    cosetRationalEuler F E L N p s = cosetRationalEuler F E M N p s := by
  by_cases hp : p.val ∣ N
  · simp only [cosetRationalEuler, ite_eq_left hp]
  simp only [cosetRationalEuler, ite_eq_right hp]
  apply Finset.prod_congr rfl
  intro P _
  congr 1
  rw [← permutation_euler_det_eq, ← permutation_euler_det_eq]
  exact permutation_euler_eq_of_character_eq L.fixingSubgroup M.fixingSubgroup hχ _ _

theorem coset_real_eq_of_permutation_characters
    (L M : IntermediateField F E)
    [NumberField.IsTotallyReal L] [NumberField.IsTotallyReal M]
    (hχ : ∀ g,
      (Representation.ofMulAction ℂ (E ≃ₐ[F] E) ((E ≃ₐ[F] E) ⧸ L.fixingSubgroup)).character g =
      (Representation.ofMulAction ℂ (E ≃ₐ[F] E) ((E ≃ₐ[F] E) ⧸ M.fixingSubgroup)).character g)
    {N : ℕ} (hN : 0 < N) (hD : (NumberField.discr E).natAbs ∣ N)
    (s : ℝ) (hs : 1 < s) :
    cosetMeromorphic (canonicalRealEmbeddings L) (degreePred_spec L) N s =
      cosetMeromorphic (canonicalRealEmbeddings M) (degreePred_spec M) N s := by
  have hs' : 1 < (s : ℂ).re := hs
  have hL := (actual_coset_meromorphic_pairing F E L (canonicalRealEmbeddings L)
    (degreePred_spec L) N hN hD).2.1 (s : ℂ) hs'
  have hM := (actual_coset_meromorphic_pairing F E M (canonicalRealEmbeddings M)
    (degreePred_spec M) N hN hD).2.1 (s : ℂ) hs'
  exact hL.unique (hM.congr_fun (fun p =>
    cosetRationalEuler_eq_of_permutation_characters L M hχ N p s))

theorem zetaZeroOrder_eq_of_permutation_characters
    (L M : IntermediateField F E)
    [NumberField.IsTotallyReal L] [NumberField.IsTotallyReal M]
    (hχ : ∀ g,
      (Representation.ofMulAction ℂ (E ≃ₐ[F] E) ((E ≃ₐ[F] E) ⧸ L.fixingSubgroup)).character g =
      (Representation.ofMulAction ℂ (E ≃ₐ[F] E) ((E ≃ₐ[F] E) ⧸ M.fixingSubgroup)).character g)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    zetaZeroOrder L β = zetaZeroOrder M β := by
  let N := (NumberField.discr E).natAbs
  have hN : 0 < N := Int.natAbs_pos.mpr (NumberField.discr_ne_zero E)
  let σ := canonicalRealEmbeddings L
  let τ := canonicalRealEmbeddings M
  have heq := analytic_off_zero_one_eq_of_real_eq
    (coset_analytic_off_zero_one σ (degreePred_spec L) N)
    (coset_analytic_off_zero_one τ (degreePred_spec M) N)
    (coset_real_eq_of_permutation_characters L M hχ hN (dvd_refl _))
  have hopen : IsOpen ({0, 1} : Set ℂ)ᶜ :=
    (Set.Finite.isClosed (by simp)).isOpen_compl
  have hβ : (β : ℂ) ∈ ({0, 1} : Set ℂ)ᶜ := by
    simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
    exact ⟨Complex.ofReal_ne_zero.mpr hβ0.ne', by exact_mod_cast hβ1.ne⟩
  have hv : cosetMeromorphic σ (degreePred_spec L) N =ᶠ[𝓝[≠] (β : ℂ)]
      cosetMeromorphic τ (degreePred_spec M) N := by
    have hu : ∀ᶠ z in 𝓝 (β : ℂ), z ∈ ({0, 1} : Set ℂ)ᶜ := hopen.mem_nhds hβ
    filter_upwards [hu.filter_mono nhdsWithin_le_nhds] with z hz
    exact heq hz
  rw [zetaZeroOrder_eq_coset_order σ (degreePred_spec L) N hβ0 hβ1,
    zetaZeroOrder_eq_coset_order τ (degreePred_spec M) N hβ0 hβ1]
  exact meromorphicOrderAt_congr hv

theorem zetaZeroOrder_fixedField_conjugate
    [NumberField.IsTotallyReal E]
    (H : Subgroup (E ≃ₐ[F] E)) (a : E ≃ₐ[F] E)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    let : NumberField.IsTotallyReal (IntermediateField.fixedField H) :=
      NumberField.IsTotallyReal.of_algebra _ E
    letI : NumberField.IsTotallyReal
        (IntermediateField.fixedField (H.map (MulAut.conj a).toMonoidHom)) :=
      NumberField.IsTotallyReal.of_algebra _ E
    zetaZeroOrder (IntermediateField.fixedField H) β =
      zetaZeroOrder (IntermediateField.fixedField (H.map (MulAut.conj a).toMonoidHom)) β := by
  let : NumberField.IsTotallyReal (IntermediateField.fixedField H) :=
    NumberField.IsTotallyReal.of_algebra _ E
  let : NumberField.IsTotallyReal
      (IntermediateField.fixedField (H.map (MulAut.conj a).toMonoidHom)) :=
    NumberField.IsTotallyReal.of_algebra _ E
  apply zetaZeroOrder_eq_of_permutation_characters _ _ _ hβ0 hβ1
  intro g
  rw [IntermediateField.fixingSubgroup_fixedField,
    IntermediateField.fixingSubgroup_fixedField]
  exact (permutation_character_conjugate_subgroup H a g).symm

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Arithmetic_StarkOddDegree
attribute [-instance] _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Odd-degree descent for real cyclic zero characters

For the application to Stark's argument it is enough to know the
restrictions of the zero character to cyclic subgroups. A real class
function with these restrictions and average one on an odd-index
subgroup is identically one. The proof uses a Sylow two-subgroup acting
on the odd set of cosets; it does not require a global Artin character.
-/

open scoped BigOperators
open PrimeDegreePackets

namespace DukePrimeDegree

/-- A real class function whose cyclic restrictions are linear characters
is trivial if it is trivial on an odd-index subgroup. -/
theorem cyclic_real_classFunction_trivial_of_odd_index
    {G : Type*} [Group G] [Finite G]
    (f : G → ℝˣ)
    (hconj : ∀ a g, f (a * g * a⁻¹) = f g)
    (hcyclic : ∀ g : G, ∃ χ : Subgroup.zpowers g →* ℝˣ,
      ∀ x : Subgroup.zpowers g, χ x = f (x : G))
    (H : Subgroup G) (hodd : Odd H.index)
    (hH : ∀ g ∈ H, f g = 1) : ∀ g, f g = 1 := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro g
  obtain ⟨χ, hχ⟩ := hcyclic g
  let C := Subgroup.zpowers g
  let P : Sylow 2 C := Classical.choice Sylow.nonempty
  let j : P →* G := C.subtype.comp P.toSubgroup.subtype
  let : MulAction P (G ⧸ H) := MulAction.compHom (G ⧸ H) j
  have hodd' : ¬ 2 ∣ Nat.card (G ⧸ H) := hodd.not_two_dvd_nat
  obtain ⟨q, hq⟩ := P.isPGroup'.nonempty_fixed_point_of_prime_not_dvd_card
    (G ⧸ H) hodd'
  obtain ⟨a, rfl⟩ := Quotient.exists_rep q
  have hP : P.toSubgroup ≤ χ.ker := by
    intro p hp
    let x : P := ⟨p, hp⟩
    have hx := hq x⁻¹
    change QuotientGroup.mk (j x⁻¹ * a) = QuotientGroup.mk a at hx
    have ha : a⁻¹ * j x * a ∈ H := by
      have ht := QuotientGroup.eq.mp hx
      simpa only [map_inv, mul_inv_rev, inv_inv, mul_assoc] using ht
    change χ p = 1
    rw [hχ]
    change f (j x) = 1
    rw [← hconj a⁻¹ (j x)]
    simpa only [inv_inv] using hH _ ha
  have hPodd : Odd P.toSubgroup.index :=
    Nat.not_even_iff_odd.mp (by
      simpa only [even_iff_two_dvd] using P.not_dvd_index)
  have ht := realFiniteCharacter_trivial_of_odd_index χ P.toSubgroup hPodd hP
  rw [← hχ ⟨g, Subgroup.mem_zpowers g⟩]
  exact ht _

/-- Average one on a subgroup forces all its values to be one, since
each real finite-order character takes only the values one and minus one. -/
theorem cyclic_real_classFunction_trivial_of_odd_average
    {G : Type*} [Group G] [Finite G]
    (f : G → ℝˣ)
    (hconj : ∀ a g, f (a * g * a⁻¹) = f g)
    (hcyclic : ∀ g : G, ∃ χ : Subgroup.zpowers g →* ℝˣ,
      ∀ x : Subgroup.zpowers g, χ x = f (x : G))
    (H : Subgroup G) [Fintype H] (hodd : Odd H.index)
    (havg : ∑ h : H, (f h : ℝ) = Fintype.card H) :
    ∀ g, f g = 1 := by
  apply cyclic_real_classFunction_trivial_of_odd_index f hconj hcyclic H hodd
  have hf (g : G) : (f g : ℝ) ≤ 1 := by
    obtain ⟨χ, hχ⟩ := hcyclic g
    have ht := realFiniteCharacter_values χ ⟨g, Subgroup.mem_zpowers g⟩
    rw [hχ] at ht
    rcases ht with ht | ht <;> simp [ht]
  have hs : ∑ h : H, (1 - (f h : ℝ)) = 0 := by
    rw [Finset.sum_sub_distrib, havg]
    simp
  have hz := (Finset.sum_eq_zero_iff_of_nonneg
    (fun (h : H) _ => sub_nonneg.mpr (hf h))).mp hs
  intro g hg
  apply Units.ext
  have ht := hz ⟨g, hg⟩ (Finset.mem_univ _)
  exact (sub_eq_zero.mp ht).symm

end DukePrimeDegree

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Arithmetic_CyclicGluing
attribute [-instance] _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Gluing the real characters selected by a simple zeta zero

A zero-order function on subgroups determines each cyclic restriction by
its values on the subgroups generated by single elements. Conjugacy of
these orders then gives precisely the class function used in odd-degree
descent. No global irreducible-character decomposition is needed.
-/

noncomputable section
open scoped BigOperators Classical

namespace DukePrimeDegree

variable {G : Type*} [Group G] [Finite G]

theorem cyclicZeroSign_eq_character
    (m : Subgroup G → ℤ) (C : Subgroup G) (χ : C →* ℝˣ)
    (hχ : ∀ x : C, m (Subgroup.zpowers (x : G)) = if χ x = 1 then 1 else 0)
    (x : C) : cyclicZeroSign m (x : G) = χ x := by
  unfold cyclicZeroSign
  rw [hχ]
  by_cases hx : χ x = 1
  · simp [hx]
  · have hv := PrimeDegreePackets.realFiniteCharacter_values χ x
    rcases hv with hv | hv
    · exact False.elim (hx hv)
    · simp only [hx, ite_false, if_false, zero_ne_one]
      exact hv.symm

theorem cyclicZeroSign_cyclic_restriction
    (m : Subgroup G → ℤ)
    (hcyclic : ∀ C : Subgroup G, IsCyclic C → ∃ χ : C →* ℝˣ,
      ∀ x : C, m (Subgroup.zpowers (x : G)) = if χ x = 1 then 1 else 0)
    (g : G) : ∃ χ : Subgroup.zpowers g →* ℝˣ,
      ∀ x : Subgroup.zpowers g, χ x = cyclicZeroSign m (x : G) := by
  obtain ⟨χ, hχ⟩ := hcyclic (Subgroup.zpowers g) inferInstance
  exact ⟨χ, fun x => (cyclicZeroSign_eq_character m _ χ hχ x).symm⟩

omit [Finite G] in
theorem cyclicZeroSign_conjugate
    (m : Subgroup G → ℤ)
    (hconj : ∀ (C : Subgroup G) (a : G), m (C.map (MulAut.conj a).toMonoidHom) = m C)
    (a g : G) : cyclicZeroSign m (a * g * a⁻¹) = cyclicZeroSign m g := by
  have hmap : (Subgroup.zpowers g).map (MulAut.conj a).toMonoidHom =
      Subgroup.zpowers (a * g * a⁻¹) := by
    rw [MonoidHom.map_zpowers]
    rfl
  unfold cyclicZeroSign
  rw [← hmap, hconj]

/-- The average of a finite real character detects its being principal. -/
theorem sum_realLinearCharacter {C : Type*} [Group C] [Fintype C]
    (χ : C →* ℝˣ) :
    (∑ g, (χ g : ℝ)) = if χ = 1 then (Fintype.card C : ℝ) else 0 := by
  by_cases hχ : χ = 1
  · simp [hχ]
  · simp only [hχ, ite_false, if_false]
    obtain ⟨a, ha⟩ : ∃ a, χ a ≠ 1 := by
      by_contra! h
      apply hχ
      exact MonoidHom.ext (fun a => by simpa using h a)
    have hval : (χ a : ℝ) ≠ 1 := fun h => ha (Units.ext h)
    have hs : (χ a : ℝ) * (∑ g, (χ g : ℝ)) = ∑ g, (χ g : ℝ) := by
      simp only [Finset.mul_sum, ← Units.val_mul, ← map_mul]
      exact Fintype.sum_equiv (Equiv.mulLeft a) _ _ (fun _ => rfl)
    by_contra hs0
    exact hval ((mul_eq_right₀ hs0).mp hs)

theorem sum_cyclicZeroSign
    (m : Subgroup G → ℤ) (C : Subgroup G) [Fintype C] (χ : C →* ℝˣ)
    (hχ : ∀ x : C, m (Subgroup.zpowers (x : G)) = if χ x = 1 then 1 else 0)
    (hC : m C = if χ = 1 then 1 else 0) :
    (∑ g : C, (cyclicZeroSign m (g : G) : ℝ)) = Fintype.card C * (m C : ℝ) := by
  simp_rw [cyclicZeroSign_eq_character m C χ hχ]
  rw [sum_realLinearCharacter, hC]
  split_ifs <;> simp

/-- The scalar form of cyclic indicator inversion for real observables. -/
theorem sum_real_eq_cyclic_sums
    {G : Type*} [Group G] [Fintype G]
    (a : CyclicSubgroups G → ℤ)
    (ha : ∀ g : G, (∑ C, if g ∈ C.val then a C else 0) = 1)
    (f : G → ℝ) :
    (∑ g, f g) = ∑ C : CyclicSubgroups G, (a C : ℝ) * ∑ g : C.val, f g := by
  have hcast (g : G) : (∑ C : CyclicSubgroups G,
      if g ∈ C.val then (a C : ℝ) else 0) = 1 := by
    exact_mod_cast ha g
  calc
    (∑ g, f g) = ∑ g, f g *
        (∑ C : CyclicSubgroups G, if g ∈ C.val then (a C : ℝ) else 0) := by
      simp only [hcast, mul_one]
    _ = ∑ C : CyclicSubgroups G, (a C : ℝ) *
        ∑ g : G, if g ∈ C.val then f g else 0 := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro C _
      apply Finset.sum_congr rfl
      intro g _
      split_ifs <;> simp [mul_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro C _
      congr 1
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype _ (by simp) f

/-- Once the cyclic averages recover the subgroup order, odd-index descent
forces all signs to be principal. -/
theorem cyclicZeroSign_trivial_of_odd_average
    (m : Subgroup G → ℤ)
    (hconj : ∀ (C : Subgroup G) (a : G), m (C.map (MulAut.conj a).toMonoidHom) = m C)
    (hcyclic : ∀ C : Subgroup G, IsCyclic C → ∃ χ : C →* ℝˣ,
      ∀ x : C, m (Subgroup.zpowers (x : G)) = if χ x = 1 then 1 else 0)
    (H : Subgroup G) [Fintype H] (hodd : Odd H.index)
    (havg : ∑ h : H, (cyclicZeroSign m (h : G) : ℝ) = Fintype.card H) :
    ∀ g, cyclicZeroSign m g = 1 :=
  cyclic_real_classFunction_trivial_of_odd_average _
    (cyclicZeroSign_conjugate m hconj)
    (cyclicZeroSign_cyclic_restriction m hcyclic) H hodd havg

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Arithmetic_ZetaCharacterRelations
attribute [-instance] _root_.AlgebraicNumberTheory.numberFieldInRationalSeparableClosure_numberField _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.finiteIdeleGroupT2Space _root_.finiteNormalClosure_numberField _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Permutation character relations give zeta-order relations

The finite character identities used in Stark descent first give local
Euler determinant identities, then incomplete zeta identities in the
half-plane of convergence, and finally integer relations on zero orders.
-/

noncomputable section
open Module Filter Set
open scoped NumberField BigOperators Classical Topology

namespace DukePrimeDegree

open PrimeDegreePackets PrimeDegreePackets.GaloisIdealCharacter

variable {F E I : Type*} [Field F] [NumberField F] [Field E] [NumberField E]
variable [Algebra F E] [FiniteDimensional F E] [IsGalois F E] [Fintype I]

theorem coset_euler_products_of_characters
    (L : I → IntermediateField F E) (p q : I → ℕ)
    (hχ : ∀ g,
      (∑ i, (p i : ℂ) * (Representation.ofMulAction ℂ (E ≃ₐ[F] E)
        ((E ≃ₐ[F] E) ⧸ (L i).fixingSubgroup)).character g) =
      ∑ i, (q i : ℂ) * (Representation.ofMulAction ℂ (E ≃ₐ[F] E)
        ((E ≃ₐ[F] E) ⧸ (L i).fixingSubgroup)).character g)
    (N : ℕ) (r : Nat.Primes) (s : ℂ) :
    (∏ i, cosetRationalEuler F E (L i) N r s ^ p i) =
      ∏ i, cosetRationalEuler F E (L i) N r s ^ q i := by
  by_cases hr : r.val ∣ N
  · simp only [cosetRationalEuler, ite_eq_left hr, one_pow, Finset.prod_const_one]
  simp only [cosetRationalEuler, ite_eq_right hr]
  simp_rw [← Finset.prod_pow]
  conv_lhs => rw [Finset.prod_comm]
  conv_rhs => rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro P _
  simp_rw [inv_pow]
  rw [Finset.prod_inv_distrib, Finset.prod_inv_distrib]
  congr 1
  simp_rw [← permutation_euler_det_eq]
  exact euler_det_products_eq_of_characters
    (V := fun i => MonoidAlgebra ℂ ((E ≃ₐ[F] E) ⧸ (L i).fixingSubgroup))
    (fun i => Representation.ofMulAction ℂ (E ≃ₐ[F] E)
      ((E ≃ₐ[F] E) ⧸ (L i).fixingSubgroup)) p q hχ _ _

theorem coset_products_of_characters
    (L : I → IntermediateField F E) [∀ i, NumberField.IsTotallyReal (L i)]
    (p q : I → ℕ)
    (hχ : ∀ g,
      (∑ i, (p i : ℂ) * (Representation.ofMulAction ℂ (E ≃ₐ[F] E)
        ((E ≃ₐ[F] E) ⧸ (L i).fixingSubgroup)).character g) =
      ∑ i, (q i : ℂ) * (Representation.ofMulAction ℂ (E ≃ₐ[F] E)
        ((E ≃ₐ[F] E) ⧸ (L i).fixingSubgroup)).character g)
    {N : ℕ} (hN : 0 < N) (hD : (NumberField.discr E).natAbs ∣ N)
    {s : ℂ} (hs : 1 < s.re) :
    (∏ i, cosetMeromorphic (canonicalRealEmbeddings (L i)) (degreePred_spec (L i)) N s ^ p i) =
      ∏ i, cosetMeromorphic (canonicalRealEmbeddings (L i)) (degreePred_spec (L i)) N s ^ q i := by
  have hp := hasProd_prod (s := Finset.univ) (fun i _ =>
    ((actual_coset_meromorphic_pairing F E (L i) (canonicalRealEmbeddings (L i))
      (degreePred_spec (L i)) N hN hD).2.1 s hs).pow (p i))
  have hq := hasProd_prod (s := Finset.univ) (fun i _ =>
    ((actual_coset_meromorphic_pairing F E (L i) (canonicalRealEmbeddings (L i))
      (degreePred_spec (L i)) N hN hD).2.1 s hs).pow (q i))
  exact hp.unique (hq.congr_fun (fun r => coset_euler_products_of_characters L p q hχ N r s))

theorem zeta_orders_of_characters
    (L : I → IntermediateField F E) [∀ i, NumberField.IsTotallyReal (L i)]
    (p q : I → ℕ)
    (hχ : ∀ g,
      (∑ i, (p i : ℂ) * (Representation.ofMulAction ℂ (E ≃ₐ[F] E)
        ((E ≃ₐ[F] E) ⧸ (L i).fixingSubgroup)).character g) =
      ∑ i, (q i : ℂ) * (Representation.ofMulAction ℂ (E ≃ₐ[F] E)
        ((E ≃ₐ[F] E) ⧸ (L i).fixingSubgroup)).character g)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    (∑ i, (p i : WithTop ℤ) * zetaZeroOrder (L i) β) =
      ∑ i, (q i : WithTop ℤ) * zetaZeroOrder (L i) β := by
  let N := (NumberField.discr E).natAbs
  have hN : 0 < N := Int.natAbs_pos.mpr (NumberField.discr_ne_zero E)
  have H := product_orders_eq_off_zero_one
    (fun i => cosetMeromorphic (canonicalRealEmbeddings (L i)) (degreePred_spec (L i)) N)
    (fun i => coset_analytic_off_zero_one _ _ N) p q
    (fun s hs => coset_products_of_characters L p q hχ hN (dvd_refl _) hs)
    (β : ℂ) (Complex.ofReal_ne_zero.mpr hβ0.ne') (by exact_mod_cast hβ1.ne)
  simpa only [← zetaZeroOrder_eq_coset_order _ _ N hβ0 hβ1] using H

theorem integer_zeta_orders_of_characters
    (L : I → IntermediateField F E) [∀ i, NumberField.IsTotallyReal (L i)]
    (c : I → ℤ)
    (hχ : ∀ g, (∑ i, (c i : ℂ) * (Representation.ofMulAction ℂ (E ≃ₐ[F] E)
      ((E ≃ₐ[F] E) ⧸ (L i).fixingSubgroup)).character g) = 0)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (m : I → ℤ) (hm : ∀ i, zetaZeroOrder (L i) β = (m i : WithTop ℤ)) :
    (∑ i, c i * m i) = 0 := by
  have hc (i : I) : (c i : ℂ) = ((c i).toNat : ℂ) - ((-c i).toNat : ℂ) := by
    exact_mod_cast (Int.toNat_sub_toNat_neg (c i)).symm
  have hrel : ∀ g,
      (∑ i, ((c i).toNat : ℂ) * (Representation.ofMulAction ℂ (E ≃ₐ[F] E)
        ((E ≃ₐ[F] E) ⧸ (L i).fixingSubgroup)).character g) =
      ∑ i, ((-c i).toNat : ℂ) * (Representation.ofMulAction ℂ (E ≃ₐ[F] E)
        ((E ≃ₐ[F] E) ⧸ (L i).fixingSubgroup)).character g := by
    intro g
    have H := hχ g
    simpa only [hc, sub_mul, Finset.sum_sub_distrib, sub_eq_zero] using H
  have H := zeta_orders_of_characters L (fun i => (c i).toNat) (fun i => (-c i).toNat)
    hrel hβ0 hβ1
  simp only [hm] at H
  have H' : (∑ i, ((c i).toNat : ℤ) * m i) = ∑ i, ((-c i).toNat : ℤ) * m i := by
    exact_mod_cast H
  calc
    (∑ i, c i * m i) =
        (∑ i, ((c i).toNat : ℤ) * m i) - ∑ i, ((-c i).toNat : ℤ) * m i := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [← sub_mul, Int.toNat_sub_toNat_neg]
    _ = 0 := sub_eq_zero.mpr H'

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Arithmetic_SubfieldOrders
attribute [-instance] _root_.AlgebraicNumberTheory.numberFieldInRationalSeparableClosure_numberField _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.finiteNormalClosure_numberField _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Integer zero orders of fixed fields

The actual continued Dedekind zeta functions have finite nonnegative
orders at real points between zero and one. Permutation character
identities therefore give ordinary integer relations on these orders.
-/

noncomputable section
open scoped NumberField BigOperators Classical

namespace DukePrimeDegree

theorem zetaZeroOrder_eq_multiplicity
    (K : Type*) [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    zetaZeroOrder K β = (zetaMultiplicity K β : WithTop ℤ) := by
  obtain ⟨m, hm⟩ := zetaZeroOrder_finite_nonnegative (K := K) hβ0 hβ1
  change zetaZeroOrder K β = ((m : ℤ) : WithTop ℤ) at hm
  simp only [zetaMultiplicity, hm, WithTop.untopD_coe]

variable {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E]
variable [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
variable [NumberField.IsTotallyReal E]

attribute [local instance] OAI.DukePrimeDegree.instIsTotallyRealSubtypeMemIntermediateFieldFixedField_solutions
theorem fixedFieldMultiplicity_conjugate
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (H : Subgroup (E ≃ₐ[F] E)) (a : E ≃ₐ[F] E) :
    fixedFieldMultiplicity β (H.map (MulAut.conj a).toMonoidHom) =
      fixedFieldMultiplicity β H := by
  unfold fixedFieldMultiplicity zetaMultiplicity
  rw [zetaZeroOrder_fixedField_conjugate H a hβ0 hβ1]

/-- An integer permutation-character relation gives the identical
relation on the orders of the corresponding fixed-field zeta functions. -/
theorem fixedFieldMultiplicity_relation
    {I : Type*} [Fintype I] (H : I → Subgroup (E ≃ₐ[F] E)) (c : I → ℤ)
    (hχ : ∀ g, (∑ i, (c i : ℂ) * (Representation.ofMulAction ℂ (E ≃ₐ[F] E)
      ((E ≃ₐ[F] E) ⧸ H i)).character g) = 0)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    (∑ i, c i * fixedFieldMultiplicity β (H i)) = 0 := by
  apply integer_zeta_orders_of_characters (fun i => IntermediateField.fixedField (H i))
    c ?_ hβ0 hβ1 (fun i => fixedFieldMultiplicity β (H i))
    (fun i => zetaZeroOrder_eq_multiplicity _ hβ0 hβ1)
  intro g
  have hfix (i : I) : (IntermediateField.fixedField (H i)).fixingSubgroup = H i :=
    IntermediateField.fixingSubgroup_fixedField (H i)
  calc
    _ = ∑ i, (c i : ℂ) * (Representation.ofMulAction ℂ (E ≃ₐ[F] E)
        ((E ≃ₐ[F] E) ⧸ H i)).character g := by
      apply Finset.sum_congr rfl
      intro i _
      exact congrArg (fun S : Subgroup (E ≃ₐ[F] E) => (c i : ℂ) *
        (Representation.ofMulAction ℂ (E ≃ₐ[F] E) ((E ≃ₐ[F] E) ⧸ S)).character g) (hfix i)
    _ = 0 := hχ g

attribute [local instance] OAI.DukePrimeDegree.instFintypeAlgEquiv_solutions_2
/-- Cyclic induction inside a subgroup controls the zero order of its
fixed field, including nonnormal intermediate fields. -/
theorem fixedFieldMultiplicity_cyclic_relation
    (H : Subgroup (E ≃ₐ[F] E)) (b : CyclicSubgroups H → ℤ)
    (hb : ∀ g : E ≃ₐ[F] E,
      (∑ C, (b C : ℂ) * (Representation.ofMulAction ℂ (E ≃ₐ[F] E)
        ((E ≃ₐ[F] E) ⧸ C.val.map H.subtype)).character g) =
      Fintype.card H * (Representation.ofMulAction ℂ (E ≃ₐ[F] E)
        ((E ≃ₐ[F] E) ⧸ H)).character g)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    (∑ C, b C * fixedFieldMultiplicity β (C.val.map H.subtype)) =
      Fintype.card H * fixedFieldMultiplicity β H := by
  let S : Option (CyclicSubgroups H) → Subgroup (E ≃ₐ[F] E)
    | none => H
    | some C => C.val.map H.subtype
  let c : Option (CyclicSubgroups H) → ℤ
    | none => -(Fintype.card H : ℤ)
    | some C => b C
  have hc : ∀ g, (∑ i, (c i : ℂ) * (Representation.ofMulAction ℂ (E ≃ₐ[F] E)
      ((E ≃ₐ[F] E) ⧸ S i)).character g) = 0 := by
    intro g
    simp only [Fintype.sum_option, S, c, Int.cast_neg, Int.cast_natCast]
    rw [hb]
    ring
  have h := fixedFieldMultiplicity_relation S c hc hβ0 hβ1
  simp only [Fintype.sum_option, S, c] at h
  linarith

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Arithmetic_StarkAverage
attribute [-instance] _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Recovering the fixed-field zero order from cyclic averages

This is the scalar form of Stark's descent: the same cyclic indicator
coefficients recover both a class-function average and the zero order of
the corresponding fixed-field zeta function.
-/

noncomputable section
open scoped BigOperators Classical NumberField

namespace DukePrimeDegree

variable {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E]
variable [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
variable [NumberField.IsTotallyReal E]

attribute [local instance] OAI.DukePrimeDegree.instFintypeAlgEquiv_solutions_3
theorem sum_eq_fixedFieldMultiplicity_of_cyclic_averages
    (f : (E ≃ₐ[F] E) → ℝ) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hcyclic : ∀ C : Subgroup (E ≃ₐ[F] E), IsCyclic C →
      (∑ g : C, f g) = Fintype.card C * (fixedFieldMultiplicity β C : ℝ))
    (H : Subgroup (E ≃ₐ[F] E)) :
    (∑ g : H, f g) = Fintype.card H * (fixedFieldMultiplicity β H : ℝ) := by
  obtain ⟨a, ha⟩ := exists_cyclic_indicator_coefficients H
  have hs (C : CyclicSubgroups H) :
      (∑ g : C.val, f (g : H)) =
        Fintype.card (C.val.map H.subtype) *
          (fixedFieldMultiplicity β (C.val.map H.subtype) : ℝ) := by
    let e := C.val.equivMapOfInjective H.subtype H.subtype_injective
    have hC : IsCyclic (C.val.map H.subtype) := e.isCyclic.mp C.property
    rw [← hcyclic _ hC]
    exact Fintype.sum_equiv e.toEquiv (fun g : C.val => f (g : H))
      (fun g : C.val.map H.subtype => f g)
      (fun _ => rfl)
  rw [sum_real_eq_cyclic_sums a ha (fun h : H => f h)]
  simp_rw [hs]
  have hord := fixedFieldMultiplicity_cyclic_relation H
    (fun C => a C * Fintype.card (C.val.map H.subtype))
    (cyclic_permutation_character_identity_inside H a ha) hβ0 hβ1
  have hcast : (∑ C : CyclicSubgroups H,
      (a C : ℝ) * Fintype.card (C.val.map H.subtype) *
        (fixedFieldMultiplicity β (C.val.map H.subtype) : ℝ)) =
      Fintype.card H * (fixedFieldMultiplicity β H : ℝ) := by
    exact_mod_cast hord
  simpa only [mul_assoc] using hcast

/-- A cyclicly linear zero-order sign function cannot have average one
on an odd-index subgroup and average zero on the full Galois group. -/
theorem no_odd_index_zero_sign_oai
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hcyclic : ∀ C : Subgroup (E ≃ₐ[F] E), IsCyclic C → ∃ χ : C →* ℝˣ,
      (∀ x : C, fixedFieldMultiplicity β (Subgroup.zpowers (x : E ≃ₐ[F] E)) =
        if χ x = 1 then 1 else 0) ∧
      fixedFieldMultiplicity β C = if χ = 1 then 1 else 0)
    (H : Subgroup (E ≃ₐ[F] E)) (hodd : Odd H.index)
    (hH : fixedFieldMultiplicity β H = 1)
    (hG : fixedFieldMultiplicity β (⊤ : Subgroup (E ≃ₐ[F] E)) = 0) : False := by
  let m : Subgroup (E ≃ₐ[F] E) → ℤ := fixedFieldMultiplicity β
  have havg (C : Subgroup (E ≃ₐ[F] E)) :
      (∑ g : C, (cyclicZeroSign m (g : E ≃ₐ[F] E) : ℝ)) =
        Fintype.card C * (m C : ℝ) := by
    apply sum_eq_fixedFieldMultiplicity_of_cyclic_averages
      (fun g : E ≃ₐ[F] E => (cyclicZeroSign m g : ℝ)) hβ0 hβ1 _ C
    intro D hD
    obtain ⟨χ, hχ, hprincipal⟩ := hcyclic D hD
    exact sum_cyclicZeroSign m D χ hχ hprincipal
  have htrivial := cyclicZeroSign_trivial_of_odd_average m
    (fun C a => fixedFieldMultiplicity_conjugate hβ0 hβ1 C a)
    (fun C hC => (hcyclic C hC).imp (fun _ h => h.1)) H hodd (by
      simpa only [m, hH, Int.cast_one, mul_one] using havg H)
  have htotal := havg (⊤ : Subgroup (E ≃ₐ[F] E))
  simp only [htrivial, Units.val_one, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one, m, hG, Int.cast_zero, mul_zero] at htotal
  have hcard : (Fintype.card (⊤ : Subgroup (E ≃ₐ[F] E)) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero (α := (⊤ : Subgroup (E ≃ₐ[F] E)))
  exact hcard htotal

end DukePrimeDegree

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.DukePrimeDegree.no_odd_index_zero_sign_oai.{u_1, u_2} := @OAI.DukePrimeDegree.no_odd_index_zero_sign_oai.{u_1, u_2}
