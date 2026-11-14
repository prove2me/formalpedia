-- Prove2me | solution 1 for OAI.PrimeDegreePackets.HeckeMellin.dedekindXiZeros_ne_zero_totallyReal
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T06:45:20.621142+00:00
-- url     : https://prove2.me/submissions/6b574689-3f86-4b7f-ac2b-23ed304536ab

import Mathlib
import Definitions.Def_DukePrimeDegree
import Definitions.Def_OAIQ244Duke023
import Definitions.Def_OAIQ244Duke024
import Theorems.Thm_OAI_PrimeDegreePackets_HeckeMellin_completedThetaXi_entire
import Theorems.Thm_OAI_PrimeDegreePackets_HeckeMellin_completedThetaXi_functionalEquation_totallyReal
import Theorems.Thm_OAI_PrimeDegreePackets_HeckeMellin_fractionalIdealTheta_mellin_lintegral_totallyReal
import Theorems.Thm_OAI_PrimeDegreePackets_ThetaConstruction_normalizedTheta_hasMellin

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
attribute [-instance] _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space
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

lemma dedekindZeta_real_nonneg (K : Type*) [Field K] [NumberField K] (s : ℝ) :
    0 ≤ (NumberField.dedekindZeta K s).re := by
  rw [dedekindZeta_real_eq_terms]
  exact tsum_nonneg (realDirichletTerm_nonneg (idealCoefficientReal_nonneg K) s)

end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_ZetaResidues
attribute [-instance] _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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



lemma tsum_idealClassPartition (K : Type*) [Field K] [NumberField K]
    (F : (FractionalIdeal (𝓞 K)⁰ K)ˣ → ℝ≥0∞) :
    (∑' c : ClassGroup (𝓞 K), ∑' J : integralIdealClassFiber (classRepresentative K c), F J.1) =
      ∑' J : integralFractionalIdeals K, F J.1 := by
  calc
    _ = ∑' x : (Σ c : ClassGroup (𝓞 K), integralIdealClassFiber (classRepresentative K c)), F x.2.1 :=
      (ENNReal.tsum_sigma' (fun x : (Σ c : ClassGroup (𝓞 K), integralIdealClassFiber (classRepresentative K c)) => F x.2.1)).symm
    _ = _ := (idealClassPartitionEquiv K).tsum_eq (fun J : integralFractionalIdeals K => F J.val)



lemma tsum_integralFractionalIdeals (K : Type*) [Field K] [NumberField K]
    (F : FractionalIdeal (𝓞 K)⁰ K → ℝ≥0∞) :
    (∑' J : integralFractionalIdeals K, F J.1) = ∑' J : {J : Ideal (𝓞 K) // J ≠ ⊥}, F J.1 :=
  ((integralFractionalIdealsEquiv K).tsum_eq (fun J => F J.1)).symm



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
attribute [-instance] _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space
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

lemma gammaHalf_hasDerivAt {s : ℂ} (hs : 0 < s.re) :
    HasDerivAt (fun z : ℂ => Complex.Gamma (z/2))
      (deriv Complex.Gamma (s/2) / 2) s := by
  have h := (Complex.differentiableAt_Gamma (s/2)
    (half_ne_nonpositive_integer hs)).hasDerivAt.comp s
      ((hasDerivAt_id s).div_const 2)
  simpa only [Function.comp_def,div_eq_mul_inv,id_eq,one_mul] using h

end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_XiBoundary
attribute [-instance] _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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
open NumberField Finset
open NumberField Filter Set Topology
namespace PrimeDegreePackets

lemma completedXiBoundaryValue_ne_zero (K : Type*) [Field K] [NumberField K] :
    completedXiBoundaryValue K ≠ 0 := by
  unfold completedXiBoundaryValue
  exact mul_ne_zero (mul_ne_zero (completionExponential_ne_zero _ _ _)
    (pow_ne_zero _ (Complex.Gamma_ne_zero (half_ne_nonpositive_integer
      (s := 1) (by norm_num)))))
    (Complex.ofReal_ne_zero.mpr (NumberField.dedekindZeta_residue_ne_zero K))

lemma tendsto_completedXi_from_right (K : Type*) [Field K] [NumberField K] :
    Tendsto (fun s : ℝ => totallyRealCompletedXi K (s:ℂ)) (𝓝[>] 1)
      (𝓝 (completedXiBoundaryValue K)) := by
  let n := Module.finrank ℚ K
  let D := |(NumberField.discr K : ℝ)|
  have hE : ContinuousAt (fun t : ℝ => completionExponential n D (t:ℂ)) 1 :=
    ContinuousAt.comp (f := Complex.ofReal) ((completionExponential_hasDerivAt n D (1:ℂ)).continuousAt)
      Complex.continuous_ofReal.continuousAt
  have hG : ContinuousAt (fun t : ℝ => Complex.Gamma ((t:ℂ)/2)^n) 1 :=
    (ContinuousAt.comp (f := Complex.ofReal)
      (gammaHalf_hasDerivAt (s := (1:ℂ)) (by norm_num)).continuousAt
      Complex.continuous_ofReal.continuousAt).pow n
  have hP := (Complex.continuous_ofReal.continuousAt.mul hE).mul hG
  have H := (hP.tendsto.mono_left nhdsWithin_le_nhds).mul
    (NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT K)
  convert H using 1
  · funext s
    dsimp only [totallyRealCompletedXi,n,D,Pi.mul_apply]
    ring
  · simp only [completedXiBoundaryValue,Pi.mul_apply,Complex.ofReal_one,one_mul,n,D]

end PrimeDegreePackets

open MeasureTheory ProbabilityTheory Matrix
open scoped Classical BigOperators ENNReal
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_CoordinateLattices
attribute [-instance] _root_.CyclicCohomology.permutationSublattice_discreteTopology _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.finiteIdeleGroupT2Space _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space
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

lemma thetaRemainder_eq (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    {t : ℝ} (ht : 0 < t) : thetaRemainder B t = latticeTheta B t - 1 := by
  classical
  let f := fun z : d → ℤ => Complex.exp (-(t:ℂ)*‖B (euclideanInteger z)‖^2)
  have H := (latticeTheta_summable B t ht).tsum_eq_add_tsum_ite 0
  have Hz : euclideanInteger (0 : d → ℤ) = 0 := by ext i; simp [euclideanInteger,integerVector]
  have H0 : f 0 = 1 := by simp [f,Hz]
  change latticeTheta B t = f 0 + ∑' z, if z = 0 then 0 else f z at H
  rw [H0] at H
  have HE : thetaRemainder B t = ∑' z, if z = 0 then 0 else f z := by
    change (∑' z : {z : d → ℤ | z ≠ 0}, f z.1) = _
    rw [tsum_subtype {z : d → ℤ | z ≠ 0} f]
    apply tsum_congr
    intro z
    by_cases hz : z = 0 <;> simp [hz,f]
  rw [HE]
  exact eq_sub_iff_add_eq.mpr ((add_comm _ _).trans H.symm)

end PrimeDegreePackets.ThetaConstruction
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_LatticeTheta
attribute [-instance] _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space
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


namespace PrimeDegreePackets.ThetaConstruction
variable {d : Type*} [Fintype d]

lemma thetaMellinXi_eq (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    {s : ℂ} (hs : s ≠ 0) (hsa : s ≠ (Fintype.card d:ℂ)/2) :
    thetaMellinXi B s = s*(s-(Fintype.card d:ℂ)/2)*thetaMellinContinuation B s := by
  unfold thetaMellinXi thetaMellinContinuation
  generalize (Fintype.card d:ℂ)/2 = a at hsa ⊢
  field_simp [hs,sub_ne_zero.mpr hsa]

end PrimeDegreePackets.ThetaConstruction

open Module MeasureTheory


namespace PrimeDegreePackets.ThetaConstruction
variable {d : Type*} [Fintype d]

lemma thetaRemainder_eq_real_sum (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    {t : ℝ} (_ht : 0 < t) : thetaRemainder B (Real.pi*t) =
      ((∑' z : NonzeroIntegerVector d, Real.exp (-latticeEnergy B z*t)):ℝ) := by
  unfold thetaRemainder
  rw [Complex.ofReal_tsum]
  congr 1
  funext z
  rw [Complex.ofReal_exp]
  congr 1
  simp only [latticeEnergy,Complex.ofReal_mul,Complex.ofReal_neg,Complex.ofReal_pow]
  ring

end PrimeDegreePackets.ThetaConstruction
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_ThetaTails
attribute [-instance] _root_.CyclicCohomology.permutationSublattice_discreteTopology _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space
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

theorem orderedThetaLogDomain_fundamental {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K) :
    IsAddFundamentalDomain (orderedLogSubgroup σ ⊤) (orderedThetaLogDomain σ) volume :=
  ZLattice.isAddFundamentalDomain (Module.Free.chooseBasis ℤ (orderedLogSubgroup σ ⊤)) volume

end PrimeDegreePackets


end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_RadialIntegrals
attribute [-instance] _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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
namespace PrimeDegreePackets.HeckeMellin
open ThetaConstruction



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


lemma rpow_cancel_ennreal_factor {x : ℝ} (hx : 0 < x) (s : ℝ)
    {C : ℝ} (hC : 0 ≤ C) (T : ℝ≥0∞) :
    ENNReal.ofReal (x^s) * (2*ENNReal.ofReal (C*x^(-s))*T) = 2*ENNReal.ofReal C*T := by
  rw [ENNReal.ofReal_mul hC]
  calc
    _ = (2*ENNReal.ofReal C) * (ENNReal.ofReal (x^s)*ENNReal.ofReal (x^(-s))) * T := by ac_rfl
    _ = _ := by rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hx.le _),
      ← Real.rpow_add hx, add_neg_cancel, Real.rpow_zero, ENNReal.ofReal_one, mul_one]



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

lemma normalizedTheta_sub_one_real {ι : Type*} [Fintype ι]
    (B : EuclideanSpace ℝ ι ≃L[ℝ] EuclideanSpace ℝ ι) {t : ℝ} (ht : 0 < t) :
    normalizedTheta B t-1 = ((normalizedTheta B t-1).re : ℂ) := by
  rw [normalizedTheta, ← thetaRemainder_eq B (mul_pos Real.pi_pos ht),
    thetaRemainder_eq_real_sum B ht, Complex.ofReal_re]

lemma normalizedTheta_sub_one_re_nonneg {ι : Type*} [Fintype ι]
    (B : EuclideanSpace ℝ ι ≃L[ℝ] EuclideanSpace ℝ ι) {t : ℝ} (ht : 0 < t) :
    0 ≤ (normalizedTheta B t-1).re := by
  rw [normalizedTheta, ← thetaRemainder_eq B (mul_pos Real.pi_pos ht),
    thetaRemainder_eq_real_sum B ht, Complex.ofReal_re]
  exact tsum_nonneg (fun _ => (Real.exp_pos _).le)

lemma norm_normalizedTheta_sub_one {ι : Type*} [Fintype ι]
    (B : EuclideanSpace ℝ ι ≃L[ℝ] EuclideanSpace ℝ ι) {t : ℝ} (ht : 0 < t) :
    ‖normalizedTheta B t-1‖ = (normalizedTheta B t-1).re := by
  conv_lhs => rw [normalizedTheta_sub_one_real B ht]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (normalizedTheta_sub_one_re_nonneg B ht)]


lemma measurable_idealThetaMellinKernel {d : ℕ} {K : Type*} [Field K] [NumberField K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) :
    Measurable (idealThetaMellinKernel σ hn I s) := by
  unfold idealThetaMellinKernel
  apply Measurable.mul (by fun_prop)
  apply Measurable.sub _ measurable_const
  unfold normalizedTheta latticeTheta
  apply Measurable.tsum
  intro z
  have HB : Measurable (fun p : ℝ × LogCoordinates d =>
      (logScaledLattice (fullLatticeEuclideanBasis (fractionalIdealFullLattice hn I) σ hn)
        (restoredLogCoordinates p.2)) (euclideanInteger z)) :=
    (logScaledLattice_measurable_apply
    (fullLatticeEuclideanBasis (fractionalIdealFullLattice hn I) σ hn)
    restoredLogCoordinates (fun i => (restoredLogCoordinates_continuous i).measurable)
    (euclideanInteger z)).comp (measurable_snd (α := ℝ))
  fun_prop

lemma norm_idealThetaMellinKernel {d : ℕ} {K : Type*} [Field K] [NumberField K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ)
    {t : ℝ} (ht : 0 < t) (u : LogCoordinates d) :
    ‖idealThetaMellinKernel σ hn I s (t,u)‖ = t^((d+1 : ℝ)*s.re/2-1) *
      (normalizedTheta
        (logScaledLattice (fullLatticeEuclideanBasis (fractionalIdealFullLattice hn I) σ hn)
          (restoredLogCoordinates u)) t-1).re := by
  unfold idealThetaMellinKernel
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht, norm_normalizedTheta_sub_one _ ht]
  simp

lemma lintegral_norm_idealThetaMellinKernel {d : ℕ} {K : Type*} [Field K] [NumberField K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) (S : Set (LogCoordinates d)) :
    (∫⁻ p, ENNReal.ofReal ‖idealThetaMellinKernel σ hn I s p‖
      ∂(volume.restrict (Ioi 0)).prod (volume.restrict S)) =
      nonnegativeIdealThetaMellin σ hn S I s.re := by
  rw [lintegral_prod _ (measurable_idealThetaMellinKernel σ hn I s).norm.ennreal_ofReal.aemeasurable]
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp only
  simp_rw [norm_idealThetaMellinKernel σ hn I s ht,
    ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _)]
  exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top



end PrimeDegreePackets.HeckeMellin
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_IdealThetaXi
attribute [-instance] _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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


lemma idealThetaMellinKernel_real {d : ℕ} {K : Type*} [Field K] [NumberField K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℝ)
    {t : ℝ} (ht : 0 < t) (u : LogCoordinates d) :
    idealThetaMellinKernel σ hn I s (t,u) =
      (‖idealThetaMellinKernel σ hn I s (t,u)‖ : ℂ) := by
  rw [norm_idealThetaMellinKernel σ hn I s ht]
  simp only [Complex.ofReal_re]
  rw [Complex.ofReal_mul, Complex.ofReal_cpow ht.le]
  unfold idealThetaMellinKernel
  simp only [Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_mul,
    Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_one, Complex.ofReal_ofNat,
    Nat.cast_add, Nat.cast_one]
  rw [normalizedTheta_sub_one_real _ ht]
  simp only [Complex.ofReal_re]

 

lemma idealThetaMellinIntegral_real {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (S : Set (LogCoordinates d)) (s : ℝ) :
    (∫ p, idealThetaMellinKernel σ hn I s p
      ∂(volume.restrict (Ioi 0)).prod (volume.restrict S)) =
      ((nonnegativeIdealThetaMellin σ hn S I s).toReal : ℂ) := by
  calc
    _ = ∫ p, (‖idealThetaMellinKernel σ hn I s p‖ : ℂ)
        ∂(volume.restrict (Ioi 0)).prod (volume.restrict S) := by
      apply integral_congr_ae
      filter_upwards [Measure.quasiMeasurePreserving_fst.ae
        (ae_restrict_mem measurableSet_Ioi)] with p hp
      exact idealThetaMellinKernel_real σ hn I s hp p.2
    _ = ((∫ p, ‖idealThetaMellinKernel σ hn I s p‖
        ∂(volume.restrict (Ioi 0)).prod (volume.restrict S) : ℝ) : ℂ) :=
      integral_complex_ofReal
    _ = _ := by
      rw [integral_eq_lintegral_of_nonneg_ae
        (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
        (measurable_idealThetaMellinKernel σ hn I s).norm.aestronglyMeasurable,
        lintegral_norm_idealThetaMellinKernel]
      rfl

end PrimeDegreePackets.HeckeMellin


namespace PrimeDegreePackets.HeckeMellin
open ThetaConstruction

lemma dedekindZeta_real_value (K : Type*) [Field K] [NumberField K] (s : ℝ) :
    ((NumberField.dedekindZeta K s).re : ℂ) = NumberField.dedekindZeta K s := by
  rw [← idealDirichlet_eq_dedekindZeta K s]
  simp



end PrimeDegreePackets.HeckeMellin

open Set
namespace PrimeDegreePackets.HeckeMellin

lemma hecke_factor_cancellation (n : ℕ) (hn : n ≠ 0) (s p g : ℂ) :
    ((2:ℂ)^n/n) * ((n*s/2)*(n*s/2-n/2)) *
      (2*(2/n*((1/2:ℂ)*p*g)^n)) = s*(s-1)*p^n*g^n := by
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have h2n : (2 : ℂ)^n ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [mul_pow, mul_pow, div_pow, one_pow]
  field_simp



end PrimeDegreePackets.HeckeMellin


namespace PrimeDegreePackets.HeckeMellin
open ThetaConstruction

lemma realHeckeFactor_ofReal (n : ℕ) (s : ℝ) :
    (realHeckeFactor n s : ℂ) =
      (2/(n : ℂ))*((1/2 : ℂ)*(Real.pi : ℂ)^(-(s : ℂ)/2)*Complex.Gamma (s/2))^n := by
  unfold realHeckeFactor
  rw [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_pow,
    Complex.ofReal_mul, Complex.ofReal_mul,
    Complex.ofReal_cpow Real.pi_pos.le, ← Complex.Gamma_ofReal]
  push_cast
  simp only [neg_div]

lemma conductor_pi_factor (n : ℕ) (D : ℝ) (s : ℂ) :
    Complex.exp (s*(Real.log D : ℂ)/2) * ((Real.pi : ℂ)^(-s/2))^n =
      completionExponential n D s := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero),
    ← Complex.ofReal_log Real.pi_pos.le, ← Complex.exp_nat_mul, ← Complex.exp_add]
  unfold completionExponential
  congr 1
  ring



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
-- module Solutions.OAIQ244_DUKE.PrimePackets_RealMellin
attribute [-instance] _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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
open ThetaConstruction

theorem classTheta_mellin_lintegral_totallyReal {d : ℕ} {K : Type*}
    [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    
    {S : Set (LogCoordinates d)} (hS : IsAddFundamentalDomain (orderedLogSubgroup σ ⊤) S volume)
    {s : ℝ} (hs : 1 < s) :
    (∑' c : ClassGroup (𝓞 K),
      ENNReal.ofReal ((FractionalIdeal.absNorm (classRepresentative K c).val : ℝ)^s) *
        nonnegativeIdealThetaMellin σ hn S (classRepresentative K c) s) =
      2 * ENNReal.ofReal (realHeckeFactor (d+1) s) *
        ENNReal.ofReal ((NumberField.dedekindZeta K s).re) := by
  have hs0 : 0 < s := lt_trans zero_lt_one hs
  simp only [nonnegativeIdealThetaMellin,
    fractionalIdealTheta_mellin_lintegral_totallyReal σ hn  _ hS hs0]
  simp_rw [rpow_cancel_ennreal_factor (fractionalIdeal_absNorm_pos _)
    s (realHeckeFactor_nonneg _ hs0)]
  rw [ENNReal.tsum_mul_left, tsum_idealClassPartition K (fun J =>
    ENNReal.ofReal ((FractionalIdeal.absNorm J.val : ℝ)^(-s))),
    integralFractionalIdeals_norm_tsum hs]

end PrimeDegreePackets.HeckeMellin


namespace PrimeDegreePackets.HeckeMellin
open ThetaConstruction

lemma nonnegativeIdealThetaMellin_ne_top_totallyReal {d : ℕ} {K : Type*}
    [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
     (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {S : Set (LogCoordinates d)} (hS : IsAddFundamentalDomain (orderedLogSubgroup σ ⊤) S volume)
    {s : ℝ} (hs : 1 < s) : nonnegativeIdealThetaMellin σ hn S I s ≠ ⊤ := by
  rw [nonnegativeIdealThetaMellin,
    fractionalIdealTheta_mellin_lintegral_totallyReal σ hn  I hS (lt_trans zero_lt_one hs)]
  exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top)
    (idealClass_norm_tsum_ne_top I hs)

theorem integrable_idealThetaMellinKernel_totallyReal {d : ℕ} {K : Type*}
    [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
     (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {S : Set (LogCoordinates d)} (hS : IsAddFundamentalDomain (orderedLogSubgroup σ ⊤) S volume)
    {s : ℂ} (hs : 1 < s.re) :
    Integrable (idealThetaMellinKernel σ hn I s)
      ((volume.restrict (Ioi 0)).prod (volume.restrict S)) := by
  refine ⟨(measurable_idealThetaMellinKernel σ hn I s).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_norm, lintegral_norm_idealThetaMellinKernel]
  exact lt_top_iff_ne_top.mpr (nonnegativeIdealThetaMellin_ne_top_totallyReal σ hn  I hS hs)

end PrimeDegreePackets.HeckeMellin


namespace PrimeDegreePackets.HeckeMellin
open ThetaConstruction

lemma idealThetaXi_eq_integral_totallyReal {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1) 
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ} (hs : 1 < s.re) :
    idealThetaXi σ hn I s =
      ((((d+1 : ℕ) : ℂ)*s/2)*(((d+1 : ℕ) : ℂ)*s/2-((d+1 : ℕ) : ℂ)/2)) *
      ∫ p, idealThetaMellinKernel σ hn I s p
        ∂(volume.restrict (Ioi 0)).prod (volume.restrict (orderedThetaLogDomain σ)) := by
  let z : ℂ := ((d+1 : ℕ) : ℂ)*s/2
  have hzre : ((d+1 : ℕ) : ℝ)/2 < z.re := by
    dsimp [z]
    simp only [Complex.div_ofNat_re, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
      zero_mul, sub_zero]
    have hd : (0 : ℝ) < d+1 := by positivity
    push_cast
    nlinarith
  have hz : z ≠ 0 := by
    intro H
    rw [H, Complex.zero_re] at hzre
    have : (0 : ℝ) ≤ ((d+1 : ℕ) : ℝ)/2 := by positivity
    linarith
  have hza : z ≠ ((d+1 : ℕ) : ℂ)/2 := by
    intro H
    simp only [H, Complex.div_ofNat_re, Complex.natCast_re] at hzre
    exact (lt_irrefl _ hzre)
  have HF := integrable_idealThetaMellinKernel_totallyReal σ hn  I
    (orderedThetaLogDomain_fundamental σ) hs
  rw [integral_prod_symm _ HF]
  unfold idealThetaXi
  calc
    _ = ∫ u in orderedThetaLogDomain σ,
        (z*(z-((d+1 : ℕ) : ℂ)/2))*
          ∫ t in Ioi 0, idealThetaMellinKernel σ hn I s (t,u) := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro u
      dsimp only
      rw [thetaMellinXi_eq _ hz (by simpa only [Fintype.card_fin] using hza)]
      have HM := (normalizedTheta_hasMellin
        (logScaledLattice (fullLatticeEuclideanBasis (fractionalIdealFullLattice hn I) σ hn)
          (restoredLogCoordinates u)) (s := z)
        (by simpa only [Fintype.card_fin] using hzre)).2
      rw [← HM]
      simp only [Fintype.card_fin, mellin, smul_eq_mul, idealThetaMellinKernel, z]
    _ = _ := integral_const_mul _ _

end PrimeDegreePackets.HeckeMellin


namespace PrimeDegreePackets.HeckeMellin
open ThetaConstruction

lemma classTheta_mellin_integral_real_totallyReal {d : ℕ} {K : Type*}
    [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
     {s : ℝ} (hs : 1 < s) :
    (∑ c : ClassGroup (𝓞 K),
      (FractionalIdeal.absNorm (classRepresentative K c).val : ℝ)^s *
      (nonnegativeIdealThetaMellin σ hn (orderedThetaLogDomain σ)
        (classRepresentative K c) s).toReal) =
      2 * realHeckeFactor (d+1) s * (NumberField.dedekindZeta K s).re := by
  have H := congrArg ENNReal.toReal (classTheta_mellin_lintegral_totallyReal σ hn 
    (orderedThetaLogDomain_fundamental σ) hs)
  have HT (c : ClassGroup (𝓞 K)) :
      ENNReal.ofReal ((FractionalIdeal.absNorm (classRepresentative K c).val : ℝ)^s) *
        nonnegativeIdealThetaMellin σ hn (orderedThetaLogDomain σ) (classRepresentative K c) s ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (nonnegativeIdealThetaMellin_ne_top_totallyReal σ hn  _ (orderedThetaLogDomain_fundamental σ) hs)
  rw [ENNReal.tsum_toReal_eq HT] at H
  simpa only [tsum_fintype, ENNReal.toReal_mul, ENNReal.toReal_ofReal
    (Real.rpow_nonneg (fractionalIdeal_absNorm_pos _).le _), ENNReal.toReal_ofNat,
    ENNReal.toReal_ofReal (realHeckeFactor_nonneg _ (lt_trans zero_lt_one hs)),
    ENNReal.toReal_ofReal (dedekindZeta_real_nonneg K s)] using H

theorem classThetaXi_real_eq_totallyReal {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1)  {s : ℝ} (hs : 1 < s) :
    classThetaXi σ hn s =
      ((((d+1 : ℕ) : ℂ)*s/2)*(((d+1 : ℕ) : ℂ)*s/2-((d+1 : ℕ) : ℂ)/2)) *
      (2*realHeckeFactor (d+1) s : ℝ) * NumberField.dedekindZeta K s := by
  let A : ℂ := (((d+1 : ℕ) : ℂ)*s/2)*(((d+1 : ℕ) : ℂ)*s/2-((d+1 : ℕ) : ℂ)/2)
  calc
    _ = ∑ c : ClassGroup (𝓞 K),
        A * (((FractionalIdeal.absNorm (classRepresentative K c).val : ℝ)^s *
          (nonnegativeIdealThetaMellin σ hn (orderedThetaLogDomain σ)
            (classRepresentative K c) s).toReal : ℝ) : ℂ) := by
      unfold classThetaXi
      apply Finset.sum_congr rfl
      intro c _
      rw [idealThetaXi_eq_integral_totallyReal σ hn  _ (by simpa using hs),
        idealThetaMellinIntegral_real, ← Complex.ofReal_cpow (fractionalIdeal_absNorm_pos _).le,
        Complex.ofReal_mul]
      dsimp [A]
      ring
    _ = A * (((∑ c : ClassGroup (𝓞 K),
        (FractionalIdeal.absNorm (classRepresentative K c).val : ℝ)^s *
          (nonnegativeIdealThetaMellin σ hn (orderedThetaLogDomain σ)
            (classRepresentative K c) s).toReal) : ℝ) : ℂ) := by
      rw [← Finset.mul_sum, Complex.ofReal_sum]
    _ = _ := by
      rw [classTheta_mellin_integral_real_totallyReal σ hn  hs, Complex.ofReal_mul,
        dedekindZeta_real_value]
      simp only [A, mul_assoc]

end PrimeDegreePackets.HeckeMellin


namespace PrimeDegreePackets.HeckeMellin
open ThetaConstruction

lemma completedThetaXi_real_eq_totallyReal {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1)  {s : ℝ} (hs : 1 < s) :
    completedThetaXi σ hn s = totallyRealCompletedXi K s := by
  unfold completedThetaXi
  rw [classThetaXi_real_eq_totallyReal σ hn  hs, Complex.ofReal_mul, Complex.ofReal_ofNat,
    realHeckeFactor_ofReal]
  let E : ℂ := Complex.exp ((s : ℂ)*(Real.log |(NumberField.discr K : ℝ)| : ℂ)/2)
  let P : ℂ := (Real.pi : ℂ)^(-(s : ℂ)/2)
  let G : ℂ := Complex.Gamma ((s : ℂ)/2)
  have H := hecke_factor_cancellation (d+1) (by omega) (s : ℂ) P G
  calc
    _ = E * (((2:ℂ)^(d+1)/((d+1 : ℕ) : ℂ)) *
        ((((d+1 : ℕ) : ℂ)*s/2)*(((d+1 : ℕ) : ℂ)*s/2-((d+1 : ℕ) : ℂ)/2)) *
        (2*(2/((d+1 : ℕ) : ℂ)*((1/2:ℂ)*P*G)^(d+1)))) * NumberField.dedekindZeta K s := by
      dsimp [E,P,G]
      ring
    _ = E * ((s : ℂ)*(s-1)*P^(d+1)*G^(d+1)) * NumberField.dedekindZeta K s := by rw [H]
    _ = (s : ℂ)*(s-1)*(E*P^(d+1))*G^(d+1)*NumberField.dedekindZeta K s := by ring
    _ = _ := by
      rw [show E*P^(d+1) = completionExponential (d+1) |(NumberField.discr K : ℝ)| s from
        conductor_pi_factor _ _ _]
      simp only [totallyRealCompletedXi, hn, G]

end PrimeDegreePackets.HeckeMellin


end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_FunctionalEquation
attribute [-instance] _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.finiteIdeleGroupT2Space _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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

lemma completedThetaXi_one_totallyReal {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1)  :
    completedThetaXi σ hn 1 = completedXiBoundaryValue K := by
  have HL : Tendsto (fun r : ℝ => completedThetaXi σ hn r) (𝓝[>] 1)
      (𝓝 (completedThetaXi σ hn 1)) := by
    exact (completedThetaXi_entire σ hn 1).continuousAt.tendsto.comp
      (Complex.continuous_ofReal.continuousAt.tendsto.mono_left inf_le_left)
  apply tendsto_nhds_unique HL
  apply (tendsto_completedXi_from_right K).congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact (completedThetaXi_real_eq_totallyReal σ hn  hr).symm

lemma completedThetaXi_zero_totallyReal {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1)  :
    completedThetaXi σ hn 0 = completedXiBoundaryValue K := by
  rw [completedThetaXi_functionalEquation_totallyReal σ hn  0, sub_zero,
    completedThetaXi_one_totallyReal σ hn ]

lemma dedekindXiZeros_ne_zero_totallyReal_oai {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1)  :
    (0 : ℂ) ∉ dedekindXiZeros σ hn := by
  change completedThetaXi σ hn 0 ≠ 0
  rw [completedThetaXi_zero_totallyReal σ hn ]
  exact completedXiBoundaryValue_ne_zero K

end PrimeDegreePackets.HeckeMellin


open IntermediateField Module

open Module IntermediateField
open scoped BigOperators NumberField Pointwise
end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.PrimeDegreePackets.HeckeMellin.dedekindXiZeros_ne_zero_totallyReal_oai.{u_1} := @OAI.PrimeDegreePackets.HeckeMellin.dedekindXiZeros_ne_zero_totallyReal_oai.{u_1}
