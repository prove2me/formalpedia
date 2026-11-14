-- Prove2me | solution 1 for OAI.DukePrimeDegree.exceptionalRealZeroExclusion_of_ray_realizations
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T06:50:25.937762+00:00
-- url     : https://prove2.me/submissions/7492704e-b951-4796-8d58-0cb611b1febe

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
import Definitions.Def_OAIQ244Duke022
import Definitions.Def_OAIQ244Duke023
import Definitions.Def_OAIQ244Duke024
import Theorems.Thm_OAI_DukePrimeDegree_exists_real_character_of_simple_zeta
import Theorems.Thm_OAI_DukePrimeDegree_extension_multiplicity_pos_of_ray_realizations
import Theorems.Thm_OAI_DukePrimeDegree_no_odd_index_positive_zero_of_cyclic_characters
import Theorems.Thm_OAI_PrimeDegreePackets_HeckeMellin_boundedDegree_near_one_zero_real_simple_unique
import Theorems.Thm_OAI_PrimeDegreePackets_HeckeMellin_completedThetaXi_eq_totallyReal
import Theorems.Thm_OAI_PrimeDegreePackets_HeckeMellin_dedekindXiZeros_ne_one_totallyReal
import Theorems.Thm_OAI_PrimeDegreePackets_HeckeMellin_dedekindXiZeros_ne_zero_totallyReal

section
-- module Solutions.OAIQ244_DUKE.Compat
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.xMeasurableSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space
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
-- module Solutions.OAIQ244_DUKE.PrimePackets_PrimeSums
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
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
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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

end PrimeDegreePackets


open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
namespace PrimeDegreePackets

open scoped NumberField nonZeroDivisors



open scoped Pointwise



open FractionalIdeal



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
-- module Solutions.OAIQ244_DUKE.PrimePackets_PacketMoments
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
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
namespace PrimeDegreePackets
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in

lemma orthoBox_preimage {n : ℕ} (u : OrthonormalBasis (Fin n) ℝ E) (a : Fin n → ℝ) :
    orthoBox u a = (fun x => WithLp.ofLp (u.repr x)) ⁻¹' Set.Icc (-a) a := by
  ext x
  simp [orthoBox,abs_le,Pi.le_def,forall_and]

lemma orthoBox_volume {n : ℕ} (u : OrthonormalBasis (Fin n) ℝ E) (a : Fin n → ℝ) :
    volume (orthoBox u a) = ∏ i, ENNReal.ofReal (2*a i) := by
  rw [orthoBox_preimage]
  have hp := (PiLp.volume_preserving_ofLp (Fin n)).comp u.measurePreserving_repr
  have H := hp.measure_preimage (measurableSet_Icc.nullMeasurableSet : NullMeasurableSet (Set.Icc (-a) a) volume)
  change volume ((WithLp.ofLp ∘ u.repr) ⁻¹' Set.Icc (-a) a) = _
  rw [H,Real.volume_Icc_pi]
  congr 1
  ext i
  simp [two_mul]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in

lemma orthoBox_convex {n : ℕ} (u : OrthonormalBasis (Fin n) ℝ E) (a : Fin n → ℝ) :
    Convex ℝ (orthoBox u a) := by
  rw [orthoBox_preimage]
  exact (convex_Icc (-a) a).linear_preimage
    ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).toLinearMap.comp u.repr.toLinearMap)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in

lemma orthoBox_symmetric {n : ℕ} (u : OrthonormalBasis (Fin n) ℝ E) (a : Fin n → ℝ)
    {x : E} (hx : x ∈ orthoBox u a) : -x ∈ orthoBox u a := by
  intro i
  simpa using hx i

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in

lemma orthoBox_norm_le {n : ℕ} (u : OrthonormalBasis (Fin n) ℝ E) (a : Fin n → ℝ)
    {x : E} (hx : x ∈ orthoBox u a) : ‖x‖ ≤ ∑ i, a i := by
  calc
    ‖x‖ = ‖∑ i, u.repr x i • u i‖ := by rw [u.sum_repr]
    _ ≤ ∑ i, ‖u.repr x i • u i‖ := norm_sum_le _ _
    _ = ∑ i, |u.repr x i| := by simp [norm_smul,u.orthonormal.1,Real.norm_eq_abs]
    _ ≤ ∑ i, a i := Finset.sum_le_sum (fun i _ => hx i)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in

lemma orthoBox_norm_le_of_zero_first {n : ℕ} (u : OrthonormalBasis (Fin (n+1)) ℝ E)
    (a : Fin (n+1) → ℝ) {x : E} (hx : x ∈ orthoBox u a) (hzero : u.repr x 0 = 0) :
    ‖x‖ ≤ ∑ i : Fin n, a i.succ := by
  calc
    ‖x‖ = ‖∑ i : Fin n, u.repr x i.succ • u i.succ‖ := by
      have H := u.sum_repr x
      rw [Fin.sum_univ_succ,hzero,zero_smul,zero_add] at H
      exact congrArg norm H.symm
    _ ≤ ∑ i : Fin n, ‖u.repr x i.succ • u i.succ‖ := norm_sum_le _ _
    _ = ∑ i : Fin n, |u.repr x i.succ| := by simp [norm_smul,u.orthonormal.1,Real.norm_eq_abs]
    _ ≤ ∑ i : Fin n, a i.succ := Finset.sum_le_sum (fun i _ => hx i.succ)

omit [MeasurableSpace E] [BorelSpace E] in
 

lemma exists_orthonormal_first_perp {n : ℕ} (hdim : finrank ℝ E = n+1)
    (W : Submodule ℝ E) (hW : W ≠ ⊤) :
    ∃ u : OrthonormalBasis (Fin (n+1)) ℝ E, ∀ x ∈ W, u.repr x 0 = 0 := by
  have hperp : Wᗮ ≠ ⊥ := fun h => hW (Submodule.orthogonal_eq_bot_iff.mp h)
  obtain ⟨v,hv,hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hperp
  let w : E := ‖v‖⁻¹ • v
  have hw : ‖w‖ = 1 := by
    simp [w,norm_smul,hv0]
  have hwW : w ∈ Wᗮ := Wᗮ.smul_mem _ hv
  have H : Orthonormal ℝ (({0} : Set (Fin (n+1))).domRestrict (fun _ => w)) := by
    rw [orthonormal_iff_ite]
    intro i j
    have hij : i = j := Subtype.ext (i.property.trans j.property.symm)
    subst j
    simp [hw]
  obtain ⟨u,hu⟩ := H.exists_orthonormalBasis_extension_of_card_eq (by simpa using hdim)
  refine ⟨u,?_⟩
  intro x hx
  rw [u.repr_apply_apply,hu 0 (by simp)]
  exact (real_inner_comm _ _).trans ((Submodule.mem_orthogonal _ _).mp hwW x hx)



open scoped Matrix
open Matrix

open TopologicalSpace
open scoped Topology

end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_CharacterPairs
attribute [-instance] _root_.CyclicCohomology.permutationSublattice_discreteTopology _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.PrimeDegreePackets.ThetaConstruction.coordinateLattice_discrete _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.periodSubmodule_addSubgroup_discrete _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
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
namespace PrimeDegreePackets
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem linear_covolume_vector_outside_subspace {n : ℕ} (hdim : finrank ℝ E = n+1)
    (V : ℝ) (hV : 0 ≤ V) :
    ∀ b : Basis (Fin (n+1)) ℝ E,
      volume (ZSpan.fundamentalDomain b) ≤ ENNReal.ofReal V →
      (∀ v ∈ Submodule.span ℤ (Set.range b), v ≠ 0 → 1 ≤ ‖v‖) →
      ∀ W : Submodule ℝ E, W ≠ ⊤ →
        ∃ v ∈ Submodule.span ℤ (Set.range b), v ∉ W ∧ ‖v‖ ≤ (2 / (1 / (2*(n+1)))^n + n / (2*(n+1))) * (V+1) := by
  let s : ℝ := 1 / (2*(n+1))
  have hs : 0 < s := by positivity
  let R : ℝ := 2*(V+1)/s^n
  have hR : 0 < R := by positivity
  intro b hb hshort W hW
  obtain ⟨u,hu⟩ := exists_orthonormal_first_perp hdim W hW
  let a : Fin (n+1) → ℝ := Fin.cons R (fun _ => s)
  have hvol : (volume (ZSpan.fundamentalDomain b))*2^(finrank ℝ E) <
      volume (orthoBox u a) := by
    apply lt_of_le_of_lt (mul_le_mul' hb (le_refl _))
    rw [hdim,orthoBox_volume,Fin.prod_univ_succ]
    simp only [a,Fin.cons_zero,Fin.cons_succ,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
    rw [← ENNReal.ofReal_pow (by positivity : 0 ≤ 2*s),
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ 2*R)]
    have H : (2*R)*(2*s)^n = (2:ℝ)^(n+1)*(2*(V+1)) := by
      dsimp [R]
      rw [mul_pow,pow_succ]
      field_simp
    rw [H,ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_pow (by norm_num)]
    norm_num only [ENNReal.ofReal_ofNat]
    rw [mul_comm (ENNReal.ofReal V)]
    apply ENNReal.mul_lt_mul_right (by positivity : (2:ℝ≥0∞)^(n+1) ≠ 0) (by finiteness)
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (by linarith)
  let L := Submodule.span ℤ (Set.range b)
  have : Countable L := inferInstance
  obtain ⟨v,hv0,hv⟩ := exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
    (L := L.toAddSubgroup)
    (ZSpan.isAddFundamentalDomain b volume) (fun x hx => orthoBox_symmetric u a hx)
    (orthoBox_convex u a) hvol
  have hvE : (v : E) ≠ 0 := by exact_mod_cast hv0
  refine ⟨v,v.property,?_,?_⟩
  · intro hvW
    have H := orthoBox_norm_le_of_zero_first u a hv (hu _ hvW)
    simp only [a,Fin.cons_succ,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
      nsmul_eq_mul] at H
    have hsε : s ≤ 1/(2*(n+1)) := le_rfl
    have Hs : (n:ℝ)*s < 1 := by
      have Hn : (n:ℝ)*s ≤ ((n:ℝ)+1)*s := by nlinarith
      have Hs : ((n:ℝ)+1)*s ≤ 1/2 := by
        have := (le_div_iff₀ (by positivity : 0 < 2*((n:ℝ)+1))).mp hsε
        nlinarith
      linarith
    exact (hshort v v.property hvE).not_gt (lt_of_le_of_lt H Hs)
  · have H := orthoBox_norm_le u a hv
    have H' : ‖(v : E)‖ ≤ R + n*s := by simpa [a,Fin.sum_univ_succ] using H
    apply H'.trans
    dsimp [R,s]
    have hns : (0:ℝ) ≤ n / (2*(n+1)) := by positivity
    have hh := mul_nonneg hns hV
    calc
      _ = (2/(1/(2*(n+1)))^n)*(V+1) + n/(2*(n+1)) := by ring
      _ ≤ (2/(1/(2*(n+1)))^n)*(V+1) + n/(2*(n+1))*(V+1) := by nlinarith
      _ = _ := by ring

theorem linear_covolume_real_basis_in_lattice {n : ℕ} (hdim : finrank ℝ E = n+1)
    (V : ℝ) (hV : 0 ≤ V) :
    ∀ b : Basis (Fin (n+1)) ℝ E,
      volume (ZSpan.fundamentalDomain b) ≤ ENNReal.ofReal V →
      (∀ v ∈ Submodule.span ℤ (Set.range b), v ≠ 0 → 1 ≤ ‖v‖) →
      ∃ c : Basis (Fin (n+1)) ℝ E,
        ∀ i, c i ∈ Submodule.span ℤ (Set.range b) ∧ ‖c i‖ ≤ (2 / (1 / (2*(n+1)))^n + n / (2*(n+1))) * (V+1) := by
  let B : ℝ := (2 / (1 / (2*(n+1)))^n + n / (2*(n+1))) * (V+1)
  have H := linear_covolume_vector_outside_subspace hdim V hV
  intro b hb hshort
  let S : Set E := {x | x ∈ Submodule.span ℤ (Set.range b) ∧ ‖x‖ ≤ B}
  have hsp : Submodule.span ℝ S = ⊤ := by
    by_contra hne
    obtain ⟨v,hv,hvW,hvB⟩ := H b hb hshort (Submodule.span ℝ S) hne
    exact hvW (Submodule.subset_span (show v ∈ S from ⟨hv,hvB⟩))
  obtain ⟨T,hTS,hTspan,hTind⟩ := exists_linearIndependent ℝ S
  have hTtop : Submodule.span ℝ T = ⊤ := hTspan.trans hsp
  let c₀ : Basis T ℝ E := Basis.mk hTind (by
    rw [Subtype.range_coe_subtype]
    change ⊤ ≤ Submodule.span ℝ T
    rw [hTtop])
  have : Finite T := hTind.finite
  let : Fintype T := Fintype.ofFinite T
  have hcard : Fintype.card T = n+1 := (finrank_eq_card_basis c₀).symm.trans hdim
  let e : T ≃ Fin (n+1) := Fintype.equivFinOfCardEq hcard
  refine ⟨c₀.reindex e,?_⟩
  intro i
  have H := hTS (e.symm i).property
  simpa [c₀,Basis.coe_reindex,S,B] using H

end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_RootOverlaps
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space
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

end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_CoordinateLattices
attribute [-instance] _root_.CyclicCohomology.permutationSublattice_discreteTopology _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue
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
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.finiteIdeleGroupT2Space _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue
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
attribute [-instance] _root_.CyclicCohomology.permutationSublattice_discreteTopology _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue
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
-- module Solutions.OAIQ244_DUKE.PrimePackets_AnalyticLogarithms
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
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
namespace PrimeDegreePackets.AnalyticGrowth

lemma entire_order_ne_top {f : ℂ → ℂ} (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0)
    (z : ℂ) : meromorphicOrderAt f z ≠ ⊤ := by
  have HM : Meromorphic f := fun z => (hf.analyticAt z).meromorphicAt
  apply HM.exists_meromorphicOrderAt_ne_top_iff_forall.mp
  use 0
  rw [(hf.analyticAt 0).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr h0]
  simp

end PrimeDegreePackets.AnalyticGrowth

open scoped Topology ComplexConjugate


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

end PrimeDegreePackets.AnalyticGrowth
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_IdealThetaXi
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue
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
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue
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

end DukePrimeDegree

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_DiscriminantBounds
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EmbeddingOrder.toRealOrder_apply
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
namespace PrimeDegreePackets

lemma integralBasis_discriminant_index {K I : Type*} [Field K] [NumberField K]
    [Fintype I] [DecidableEq I] (b : Basis I ℚ K)
    (hb : ∀ i, IsIntegral ℤ (b i)) :
    ∃ z : ℤ, z ≠ 0 ∧ Algebra.discr ℚ b = (z:ℚ)^2 * (NumberField.discr K : ℚ) := by
  classical
  let e := (NumberField.integralBasis K).indexEquiv b
  let b₀ := (NumberField.integralBasis K).reindex e
  let P := b₀.toMatrix b
  have hP : ∀ i j, IsIntegral ℤ (P i j) := by
    intro i j
    change IsIntegral ℤ ((NumberField.integralBasis K).repr (b j) (e.symm i))
    let x : 𝓞 K := ⟨b j,hb j⟩
    have hx : b j = algebraMap (𝓞 K) K x := rfl
    rw [hx,NumberField.integralBasis_repr_apply]
    exact isIntegral_algebraMap
  obtain ⟨z,hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp (IsIntegral.det hP)
  have hz0 : z ≠ 0 := by
    intro h
    have hP0 : P.det = 0 := by rw [← hz,h,_root_.map_zero]
    have hh : P.det * (b.toMatrix b₀).det = 1 := by
      rw [← Matrix.det_mul]
      simp [P]
    rw [hP0,zero_mul] at hh
    exact zero_ne_one hh
  refine ⟨z,hz0,?_⟩
  rw [← b₀.toMatrix_map_vecMul b,Algebra.discr_of_matrix_vecMul]
  change P.det ^ 2 * Algebra.discr ℚ b₀ = _
  rw [← hz]
  congr 1
  simpa only [b₀,Basis.coe_reindex,Algebra.discr_reindex] using
    (NumberField.coe_discr K).symm

 

theorem abs_discr_le_integral_basis {K I : Type*} [Field K] [NumberField K]
    [Fintype I] [DecidableEq I] (b : Basis I ℚ K)
    (hb : ∀ i, IsIntegral ℤ (b i)) :
    |(NumberField.discr K : ℝ)| ≤ |(Algebra.discr ℚ b : ℝ)| := by
  obtain ⟨z,hz,he⟩ := integralBasis_discriminant_index b hb
  have he' : (Algebra.discr ℚ b : ℝ) = (z:ℝ)^2 * (NumberField.discr K : ℝ) := by
    exact_mod_cast he
  rw [he',abs_mul,abs_pow,even_two.pow_abs]
  have hz1 : (1:ℝ) ≤ (z:ℝ)^2 := by
    have hzi : (1:ℤ) ≤ z^2 := by
      have hh : 0 < z^2 := sq_pos_of_ne_zero hz
      omega
    exact_mod_cast hzi
  nlinarith [abs_nonneg (NumberField.discr K : ℝ)]

lemma norm_det_le_factorial_pow {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) {B : ℝ} (_hB : 0 ≤ B) (hA : ∀ i j, ‖A i j‖ ≤ B) :
    ‖A.det‖ ≤ (Fintype.card I).factorial * B ^ Fintype.card I := by
  classical
  rw [Matrix.det_apply']
  calc
    ‖∑ σ : Equiv.Perm I, (Equiv.Perm.sign σ : ℂ) * ∏ i, A (σ i) i‖
        ≤ ∑ σ : Equiv.Perm I, ‖(Equiv.Perm.sign σ : ℂ) * ∏ i, A (σ i) i‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _σ : Equiv.Perm I, B ^ Fintype.card I := by
      apply Finset.sum_le_sum
      intro σ _
      rw [norm_mul]
      have hs : ‖(Equiv.Perm.sign σ : ℂ)‖ = 1 := by
        simpa only [Complex.norm_intCast] using (abs_unit_intCast (α := ℝ) (Equiv.Perm.sign σ))
      rw [hs,one_mul,norm_prod]
      exact (Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun i _ => hA (σ i) i)).trans_eq
        (by simp)
    _ = _ := by simp [Fintype.card_perm]

 

theorem abs_discr_le_integral_basis_height {K I : Type*} [Field K] [NumberField K]
    [Fintype I] [DecidableEq I] (b : Basis I ℚ K)
    (hb : ∀ i, IsIntegral ℤ (b i)) {B : ℝ} (hB : 0 ≤ B)
    (hheight : ∀ (σ : K →ₐ[ℚ] ℂ) i, ‖σ (b i)‖ ≤ B) :
    |(NumberField.discr K : ℝ)| ≤
      ((Fintype.card I).factorial * B ^ Fintype.card I)^2 := by
  classical
  let e : I ≃ (K →ₐ[ℚ] ℂ) := Fintype.equivOfCardEq (by
    rw [← finrank_eq_card_basis b,AlgHom.card])
  have he := Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two ℚ ℂ b e
  have he' : |(Algebra.discr ℚ b : ℝ)| =
      ‖(Algebra.embeddingsMatrixReindex ℚ ℂ b e).det‖^2 := by
    have h := congrArg norm he
    simpa only [norm_pow,eq_ratCast,Complex.norm_ratCast] using h
  calc
    |(NumberField.discr K : ℝ)| ≤ |(Algebra.discr ℚ b : ℝ)| := abs_discr_le_integral_basis b hb
    _ = _ := he'
    _ ≤ _ := pow_le_pow_left₀ (norm_nonneg _) (norm_det_le_factorial_pow _ hB (by
      intro i j
      exact hheight (e j) i)) 2

end PrimeDegreePackets

open Module MeasureTheory Set WithLp
open scoped NumberField BigOperators ENNReal
namespace PrimeDegreePackets


lemma integralEuclideanBasis_exists {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (σ : OrderedEmbeddings n K) (hn : finrank ℚ K = n)
    (bZ : Basis (Fin n) ℤ (𝓞 K)) :
    ∃ b : Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)),
      (∀ i, b i = orderedEuclideanMap σ (bZ i)) ∧
      volume (ZSpan.fundamentalDomain b) =
        ENNReal.ofReal (Real.sqrt |(NumberField.discr K : ℝ)|) := by
  let A : Matrix (Fin n) (Fin n) ℝ := fun i j => σ j (bZ i)
  have hdet : A.det ≠ 0 := by
    intro h
    have H := integralEmbeddingMatrix_det_sq σ hn bZ
    change A.det ^ 2 = _ at H
    rw [h,zero_pow (by norm_num)] at H
    exact NumberField.discr_ne_zero K (by exact_mod_cast H.symm)
  let bR : Basis (Fin n) ℝ (Fin n → ℝ) := (Pi.basisFun ℝ (Fin n)).map
    (Matrix.toLinearEquiv (Pi.basisFun ℝ (Fin n)) A.transpose
      (by simpa only [Matrix.det_transpose] using isUnit_iff_ne_zero.mpr hdet))
  have hbR (i j : Fin n) : bR i j = σ j (bZ i) := by
    simp [bR,Matrix.toLinearEquiv_apply,Matrix.toLin_apply,Matrix.mulVec,
      dotProduct,Pi.single_apply,A]
    rfl
  let u := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)
  let b := bR.map u.symm.toLinearEquiv
  refine ⟨b,?_,?_⟩
  · intro i
    ext j
    exact hbR i j
  · have hi : u.toLinearEquiv '' ZSpan.fundamentalDomain b =
        ZSpan.fundamentalDomain bR := by
      rw [ZSpan.map_fundamentalDomain]
      congr 1
    have hp : u ⁻¹' ZSpan.fundamentalDomain bR = ZSpan.fundamentalDomain b := by
      rw [← hi]
      exact Set.preimage_image_eq _ u.injective
    have hm := (PiLp.volume_preserving_ofLp (Fin n)).measure_preimage
      (ZSpan.fundamentalDomain_measurableSet bR).nullMeasurableSet
    change volume (u ⁻¹' ZSpan.fundamentalDomain bR) = _ at hm
    rw [hp,ZSpan.volume_fundamentalDomain] at hm
    have hd : |(Matrix.of bR).det| = Real.sqrt |(NumberField.discr K : ℝ)| := by
      have he : Matrix.of bR = A := by ext i j; exact hbR i j
      rw [he]
      conv_rhs => rw [← integralEmbeddingMatrix_det_sq σ hn bZ,
        abs_of_nonneg (sq_nonneg _),Real.sqrt_sq_eq_abs]
    simpa only [hd] using hm

lemma integralEuclideanBasis_span {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (σ : OrderedEmbeddings n K) (bZ : Basis (Fin n) ℤ (𝓞 K))
    (b : Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (hb : ∀ i, b i = orderedEuclideanMap σ (bZ i)) {v : EuclideanSpace ℝ (Fin n)}
    (hv : v ∈ Submodule.span ℤ (Set.range b)) :
    ∃ a : 𝓞 K, orderedEuclideanMap σ a = v := by
  obtain ⟨z,rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hv
  refine ⟨∑ i, z i • bZ i,?_⟩
  simp only [_root_.map_sum,map_zsmul]
  simp_rw [hb]

 

lemma orderedEuclideanMap_integer_shortest {d : ℕ} {K : Type*}
    [Field K] [NumberField K] (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1) (a : 𝓞 K) (ha : a ≠ 0) :
    1 ≤ ‖orderedEuclideanMap σ a‖ := by
  have hnorm : (1:ℝ) ≤ |(Algebra.norm ℚ (a : K) : ℝ)| := by
    rw [← Algebra.coe_norm_int]
    exact_mod_cast Int.one_le_abs (Algebra.norm_ne_zero_iff.mpr ha)
  have hprod : |(Algebra.norm ℚ (a : K) : ℝ)| ≤
      ‖orderedEuclideanMap σ a‖^(d+1) := by
    rw [← prod_abs_orderedEmbeddings σ hn]
    calc
      _ ≤ ∏ _i : Fin (d+1), ‖orderedEuclideanMap σ a‖ := by
        apply Finset.prod_le_prod (fun _ _ => abs_nonneg _)
        intro i _
        exact (Real.norm_eq_abs _).symm ▸ PiLp.norm_apply_le (orderedEuclideanMap σ a) i
      _ = _ := by simp
  by_contra h
  have hh := pow_lt_one₀ (norm_nonneg (orderedEuclideanMap σ a)) (lt_of_not_ge h) (by omega : d+1 ≠ 0)
  linarith

 

theorem totallyReal_small_integral_basis {d : ℕ} {K : Type*}
    [Field K] [NumberField K] (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1) :
    ∃ c : Basis (Fin (d+1)) ℚ K,
      (∀ i, IsIntegral ℤ (c i)) ∧
      ∀ (ρ : K →ₐ[ℚ] ℂ) i, ‖ρ (c i)‖ ≤
        (2 / (1 / (2*(d+1)))^d + d / (2*(d+1))) *
          (Real.sqrt |(NumberField.discr K : ℝ)| + 1) := by
  classical
  let bZ : Basis (Fin (d+1)) ℤ (𝓞 K) := (Module.Free.chooseBasis ℤ (𝓞 K)).reindex
    (Fintype.equivFinOfCardEq (by
      rw [← finrank_eq_card_basis (Module.Free.chooseBasis ℤ (𝓞 K)),NumberField.RingOfIntegers.rank,hn]))
  obtain ⟨b,hb,hvol⟩ := integralEuclideanBasis_exists σ hn bZ
  obtain ⟨c,hc⟩ := linear_covolume_real_basis_in_lattice
    (by simp : finrank ℝ (EuclideanSpace ℝ (Fin (d+1))) = d+1)
    (Real.sqrt |(NumberField.discr K : ℝ)|) (Real.sqrt_nonneg _)
    b hvol.le (by
      intro v hv hv0
      obtain ⟨a,rfl⟩ := integralEuclideanBasis_span σ bZ b hb hv
      apply orderedEuclideanMap_integer_shortest σ hn a
      intro ha
      apply hv0
      simp [ha])
  choose a ha using fun i => integralEuclideanBasis_span σ bZ b hb (hc i).1
  have hli : LinearIndependent ℚ (fun i => (a i : K)) := by
    apply LinearIndependent.of_comp (orderedEuclideanMap σ)
    have he : orderedEuclideanMap σ ∘ (fun i => (a i : K)) = c := funext ha
    rw [he]
    exact c.linearIndependent.restrict_scalars (by
      simpa only [Algebra.smul_def,mul_one] using (FaithfulSMul.algebraMap_injective ℚ ℝ))
  let cQ := basisOfLinearIndependentOfCardEqFinrank hli (by simpa using hn.symm)
  have he (i : Fin (d+1)) : cQ i = (a i : K) := by simp [cQ]
  refine ⟨cQ,fun i => he i ▸ (a i).prop,?_⟩
  intro ρ i
  obtain ⟨j,rfl⟩ := (orderedComplexEmbeddings σ hn).surjective ρ
  rw [he]
  change ‖(σ j (a i) : ℂ)‖ ≤ _
  rw [Complex.norm_real]
  calc
    ‖σ j (a i)‖ ≤ ‖orderedEuclideanMap σ (a i)‖ :=
      PiLp.norm_apply_le (orderedEuclideanMap σ (a i)) j
    _ = ‖c i‖ := congrArg norm (ha i)
    _ ≤ _ := (hc i).2

end PrimeDegreePackets


end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_RealMellin
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EmbeddingOrder.toRealOrder_apply
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
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EmbeddingOrder.toRealOrder_apply
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
namespace PrimeDegreePackets

lemma normalClosure_isTotallyReal {K L : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] [Field L] [CharZero L]
    [Algebra.IsAlgebraic ℚ L] :
    NumberField.IsTotallyReal (normalClosure ℚ K L) := by
  let M : IntermediateField ℚ L :=
    (NumberField.maximalRealSubfield L).toIntermediateField (fun q => by
      simp)
  have hM : normalClosure ℚ K L ≤ M := by
    rw [normalClosure_le_iff]
    intro f
    let : NumberField.IsTotallyReal f.fieldRange :=
      NumberField.IsTotallyReal.ofRingEquiv f.equivFieldRange.toRingEquiv
    exact NumberField.IsTotallyReal.le_maximalRealSubfield f.fieldRange.toSubfield
  change NumberField.IsTotallyReal (normalClosure ℚ K L).toSubfield
  exact NumberField.isTotallyReal_iff_le_maximalRealSubfield.mpr hM



lemma embeddingPermutation_injective {F K N : Type*} [Field F] [Field K] [Field N]
    [Algebra F K] [Algebra F N] [Algebra.IsAlgebraic F K]
    [IsNormalClosure F K N] :
    Function.Injective (embeddingPermutation (F := F) (K := K) (N := N)) := by
  intro σ τ h
  let E : IntermediateField F N := {
    carrier := {x | σ x = τ x}
    zero_mem' := by simp
    one_mem' := by simp
    add_mem' := by intro x y hx hy; change σ x = τ x at hx; change σ y = τ y at hy
                   change σ (x+y) = τ (x+y); simp only [map_add,hx,hy]
    mul_mem' := by intro x y hx hy; change σ x = τ x at hx; change σ y = τ y at hy
                   change σ (x*y) = τ (x*y); simp only [map_mul,hx,hy]
    inv_mem' := by intro x hx; change σ x = τ x at hx
                   change σ (x⁻¹) = τ (x⁻¹); simp only [map_inv₀,hx]
    algebraMap_mem' := by intro r; simp }
  have hE : normalClosure F K N ≤ E := by
    rw [normalClosure_le_iff]
    intro f x hx
    obtain ⟨y,rfl⟩ := hx
    exact congrArg (fun p : Equiv.Perm (K →ₐ[F] N) => p f y) h
  have ht : normalClosure F K N = ⊤ :=
    (Algebra.IsAlgebraic.isNormalClosure_iff.mp inferInstance).2
  rw [ht] at hE
  ext x
  exact hE (show x ∈ (⊤ : IntermediateField F N) from trivial)

 

theorem normalClosure_finrank_le_factorial {F K N : Type*} [Field F] [Field K] [Field N]
    [Algebra F K] [Algebra F N] [FiniteDimensional F K] [FiniteDimensional F N]
    [IsNormalClosure F K N] [IsGalois F N] :
    finrank F N ≤ (finrank F K).factorial := by
  rw [←IsGalois.card_aut_eq_finrank F N]
  calc
    Nat.card (N ≃ₐ[F] N) ≤ Nat.card (Equiv.Perm (K →ₐ[F] N)) :=
      Nat.card_le_card_of_injective _ embeddingPermutation_injective
    _ = (Nat.card (K →ₐ[F] N)).factorial := Nat.card_perm
    _ ≤ (finrank F K).factorial := Nat.factorial_le (card_algHom_le_finrank F K N)



end PrimeDegreePackets

open Module IntermediateField
open scoped BigOperators NumberField Pointwise
namespace PrimeDegreePackets

lemma subalgebra_sup_toSubmodule_mul {F N : Type*} [CommSemiring F] [CommSemiring N]
    [Algebra F N] (A B : Subalgebra F N) :
    (A ⊔ B).toSubmodule = A.toSubmodule * B.toSubmodule := by
  simpa only [Algebra.adjoin_union,Algebra.adjoin_eq] using
    Algebra.adjoin_union_coe_submodule F (A : Set N) (B : Set N)

lemma intermediate_finset_sup_toSubmodule {F N I : Type*} [Field F] [Field N]
    [Algebra F N] [Algebra.IsAlgebraic F N]
    (s : Finset I) (A : I → IntermediateField F N) :
    (s.sup A).toSubalgebra.toSubmodule = ∏ i ∈ s, (A i).toSubalgebra.toSubmodule := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Algebra.toSubmodule_bot]
  | @insert i s hi ih =>
    rw [Finset.sup_insert,Finset.prod_insert hi,
      IntermediateField.sup_toSubalgebra_of_isAlgebraic,subalgebra_sup_toSubmodule_mul,ih]
    exact Or.inl inferInstance

 

theorem normalClosure_integral_basis_height {K N I : Type*} [Field K] [NumberField K]
    [Field N] [NumberField N] [IsNormalClosure ℚ K N]
    [Fintype I] [DecidableEq I] (b : Basis I ℚ K)
    (hb : ∀ i, IsIntegral ℤ (b i)) {B : ℝ} (hB : 1 ≤ B)
    (hheight : ∀ (σ : K →ₐ[ℚ] ℂ) i, ‖σ (b i)‖ ≤ B) :
    ∃ c : Basis (Fin (finrank ℚ N)) ℚ N,
      (∀ i, IsIntegral ℤ (c i)) ∧
      ∀ (σ : N →ₐ[ℚ] ℂ) i, ‖σ (c i)‖ ≤ B ^ finrank ℚ K := by
  classical
  let S (f : K →ₐ[ℚ] N) : Set N := Set.range (fun i => f (b i))
  let P : Set N := ∏ f : K →ₐ[ℚ] N, S f
  have hspan (f : K →ₐ[ℚ] N) :
      Submodule.span ℚ (S f) = f.fieldRange.toSubalgebra.toSubmodule := by
    change Submodule.span ℚ (Set.range (f.toLinearMap ∘ b)) = _
    rw [Set.range_comp,← Submodule.map_span,b.span_eq,Submodule.map_top]
    rfl
  have htop : Submodule.span ℚ P = ⊤ := by
    unfold P
    rw [← Submodule.prod_span]
    simp_rw [hspan]
    rw [← intermediate_finset_sup_toSubmodule]
    have hn : Finset.univ.sup (fun f : K →ₐ[ℚ] N => f.fieldRange) = ⊤ := by
      rw [Finset.sup_univ_eq_iSup]
      exact (Algebra.IsAlgebraic.isNormalClosure_iff.mp inferInstance).2
    rw [hn]
    rfl
  have hP (x : N) (hx : x ∈ P) : IsIntegral ℤ x ∧
      ∀ σ : N →ₐ[ℚ] ℂ, ‖σ x‖ ≤ B ^ finrank ℚ K := by
    obtain ⟨v,hv,rfl⟩ := (Set.mem_fintype_prod S x).mp hx
    constructor
    · apply IsIntegral.prod
      intro f _
      obtain ⟨i,hi⟩ := hv f
      rw [← hi]
      exact map_isIntegral_int f (hb i)
    · intro σ
      rw [map_prod,norm_prod]
      calc
        ∏ f : K →ₐ[ℚ] N, ‖σ (v f)‖ ≤ ∏ _f : K →ₐ[ℚ] N, B := by
          apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
          intro f _
          obtain ⟨i,hi⟩ := hv f
          rw [← hi]
          exact hheight (σ.comp f) i
        _ = B ^ Fintype.card (K →ₐ[ℚ] N) := by simp
        _ ≤ B ^ finrank ℚ K := by
          apply pow_le_pow_right₀ hB
          simpa only [Fintype.card_eq_nat_card] using card_algHom_le_finrank ℚ K N
  let c₀ := Basis.ofSpan (show ⊤ ≤ Submodule.span ℚ P from htop.ge)
  let T := (linearIndepOn_empty ℚ (id : N → N)).extend (Set.empty_subset P)
  have : Finite T := c₀.linearIndependent.finite
  let : Fintype T := Fintype.ofFinite T
  let e : T ≃ Fin (finrank ℚ N) := Fintype.equivFinOfCardEq (finrank_eq_card_basis c₀).symm
  let c := c₀.reindex e
  refine ⟨c,?_,?_⟩
  · intro i
    exact (hP (c i) (Basis.ofSpan_subset (show ⊤ ≤ Submodule.span ℚ P from htop.ge) ⟨e.symm i,by simp [c,Basis.coe_reindex,c₀]⟩)).1
  · intro σ i
    exact (hP (c i) (Basis.ofSpan_subset (show ⊤ ≤ Submodule.span ℚ P from htop.ge) ⟨e.symm i,by simp [c,Basis.coe_reindex,c₀]⟩)).2 σ

 

theorem normalClosure_discr_le_basis_height {K N I : Type*}
    [Field K] [NumberField K] [Field N] [NumberField N] [IsNormalClosure ℚ K N]
    [Fintype I] [DecidableEq I] (b : Basis I ℚ K)
    (hb : ∀ i, IsIntegral ℤ (b i)) {B : ℝ} (hB : 1 ≤ B)
    (hheight : ∀ (σ : K →ₐ[ℚ] ℂ) i, ‖σ (b i)‖ ≤ B) :
    |(NumberField.discr N : ℝ)| ≤
      ((finrank ℚ N).factorial * (B ^ finrank ℚ K) ^ finrank ℚ N)^2 := by
  obtain ⟨c,hc,hheightc⟩ := normalClosure_integral_basis_height (N := N) b hb hB hheight
  simpa only [Fintype.card_fin] using abs_discr_le_integral_basis_height c hc
    (pow_nonneg (le_trans zero_le_one hB) _) hheightc

end PrimeDegreePackets


namespace PrimeDegreePackets



lemma closureDiscriminantConstant_pos (d : ℕ) : 0 < closureDiscriminantConstant d := by
  have h : 1 ≤ smallIntegralBasisConstant d := le_max_left _ _
  unfold closureDiscriminantConstant
  positivity

 

theorem normalClosure_discr_polynomial {d : ℕ} {K N : Type*}
    [Field K] [NumberField K] [Field N] [NumberField N]
    [IsNormalClosure ℚ K N]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1) :
    |(NumberField.discr N : ℝ)| ≤ closureDiscriminantConstant d *
      |(NumberField.discr K : ℝ)| ^ (2*((d+1)*(d+1).factorial)) := by
  classical
  let C := smallIntegralBasisConstant d
  have hC : 1 ≤ C := le_max_left _ _
  have hC0 : 0 ≤ C := le_trans zero_le_one hC
  let D : ℝ := |(NumberField.discr K : ℝ)|
  have hD : 1 ≤ D := by
    dsimp [D]
    exact_mod_cast Int.one_le_abs (NumberField.discr_ne_zero K)
  have hD0 : 0 ≤ D := le_trans zero_le_one hD
  let B := C * (Real.sqrt D + 1)
  have hB : 1 ≤ B := by
    have hs := Real.sqrt_nonneg D
    dsimp [B]
    nlinarith
  have hBD : B ≤ (2*C)*D := by
    have hs : Real.sqrt D ≤ D := (Real.sqrt_le_iff).2 ⟨hD0,by nlinarith⟩
    dsimp [B]
    nlinarith
  obtain ⟨b,hb,hheight⟩ := totallyReal_small_integral_basis σ hn
  have hheightB : ∀ (ρ : K →ₐ[ℚ] ℂ) i, ‖ρ (b i)‖ ≤ B := by
    intro ρ i
    apply (hheight ρ i).trans
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  have hfirst := normalClosure_discr_le_basis_height (N := N) b hb hB hheightB
  let : Normal ℚ N := IsNormalClosure.normal (K := K)
  let : IsGalois ℚ N := {}
  have hm : finrank ℚ N ≤ (d+1).factorial := by
    simpa only [hn] using (normalClosure_finrank_le_factorial (F := ℚ) (K := K) (N := N))
  have hBB : 1 ≤ (2*C)*D := hB.trans hBD
  have hp : (B ^ finrank ℚ K) ^ finrank ℚ N ≤
      ((2*C)*D)^((d+1)*(d+1).factorial) := by
    rw [hn,← pow_mul]
    exact (pow_le_pow_left₀ (le_trans zero_le_one hB) hBD _).trans
      (pow_le_pow_right₀ hBB (Nat.mul_le_mul_left _ hm))
  have hf : ((finrank ℚ N).factorial : ℝ) ≤ (((d+1).factorial).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le hm
  calc
    |(NumberField.discr N : ℝ)| ≤
      ((finrank ℚ N).factorial * (B ^ finrank ℚ K) ^ finrank ℚ N)^2 := hfirst
    _ ≤ ((((d+1).factorial).factorial : ℝ) *
        ((2*C)*D)^((d+1)*(d+1).factorial))^2 := by
      apply pow_le_pow_left₀ (by positivity)
      exact mul_le_mul hf hp (by positivity) (by positivity)
    _ = closureDiscriminantConstant d * D ^ (2*((d+1)*(d+1).factorial)) := by
      dsimp [closureDiscriminantConstant,C]
      simp only [mul_pow]
      rw [← pow_mul]
      ring

 

theorem normalClosure_log_discr_uniform (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K N : Type*) [Field K] [NumberField K]
      [Field N] [NumberField N] [IsNormalClosure ℚ K N]
      (_σ : OrderedEmbeddings (d+1) K), finrank ℚ K = d+1 →
        Real.log (3*|(NumberField.discr N : ℝ)|) ≤
          C * Real.log (3*|(NumberField.discr K : ℝ)|) := by
  let A := closureDiscriminantConstant d
  let k := 2*((d+1)*(d+1).factorial)
  have hA : 0 < A := closureDiscriminantConstant_pos d
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  let C := |Real.log (3*A)| / Real.log 3 + k + 1
  have hC : 0 < C := by dsimp [C] <;> positivity
  refine ⟨C,hC,?_⟩
  intro K N _ _ _ _ _ σ hn
  let D : ℝ := |(NumberField.discr K : ℝ)|
  let DN : ℝ := |(NumberField.discr N : ℝ)|
  have hD : 1 ≤ D := by
    dsimp [D]
    exact_mod_cast Int.one_le_abs (NumberField.discr_ne_zero K)
  have hDN : 0 < DN := by
    exact abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero N)
  have hD0 : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hbound : DN ≤ A*D^k := normalClosure_discr_polynomial σ hn
  have hlog : Real.log 3 ≤ Real.log (3*D) :=
    Real.log_le_log (by norm_num) (by nlinarith)
  have hlogpos : 0 < Real.log (3*D) := h3.trans_le hlog
  have hx : |Real.log (3*A)| ≤
      (|Real.log (3*A)| / Real.log 3) * Real.log (3*D) := by
    have H := mul_le_mul_of_nonneg_left hlog
      (div_nonneg (abs_nonneg (Real.log (3*A))) h3.le)
    rwa [div_mul_cancel₀ _ h3.ne'] at H
  have hlogD : Real.log D ≤ Real.log (3*D) :=
    Real.log_le_log hD0 (by linarith)
  calc
    Real.log (3*DN) ≤ Real.log (3*(A*D^k)) :=
      Real.log_le_log (by positivity) (mul_le_mul_of_nonneg_left hbound (by norm_num))
    _ = Real.log (3*A) + k*Real.log D := by
      rw [← mul_assoc,Real.log_mul (by positivity) (by positivity),Real.log_pow]
    _ ≤ |Real.log (3*A)| + k*Real.log (3*D) :=
      add_le_add (le_abs_self _) (mul_le_mul_of_nonneg_left hlogD (by positivity))
    _ ≤ C*Real.log (3*D) := by
      dsimp [C]
      nlinarith

end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Arithmetic_RationalZeroGap
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The fixed rational-field zero gap

The final contradiction in odd-degree zero descent only needs a fixed
neighborhood of one where the rational completed zeta function is
nonzero. Continuity and its computed value at one supply that gap.
-/

open Filter Set
open scoped Topology

namespace DukePrimeDegree

open PrimeDegreePackets PrimeDegreePackets.HeckeMellin

/-- The completed zeta function of the rational field is nonzero on a
fixed real interval ending at one. -/
theorem rational_completedXi_nonzero_near_one
    (σ : OrderedEmbeddings 1 ℚ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ β ∈ Icc (1 - δ) 1,
      completedThetaXi σ (by simp : Module.finrank ℚ ℚ = 1) β ≠ 0 := by
  let f : ℂ → ℂ := completedThetaXi σ (by simp : Module.finrank ℚ ℚ = 1)
  have h1 : f 1 ≠ 0 := by
    exact dedekindXiZeros_ne_one_totallyReal σ (by simp)
  have hc : ContinuousAt (fun β : ℝ => f β) 1 :=
    (completedThetaXi_entire σ (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).continuous.continuousAt.comp
      Complex.continuous_ofReal.continuousAt
  obtain ⟨ε, hε, he⟩ := Metric.eventually_nhds_iff.mp (hc.eventually_ne h1)
  refine ⟨ε / 2, by positivity, fun β hβ => ?_⟩
  apply he
  rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hβ.2)]
  linarith [hβ.1]

/-- A fixed rational-field zero gap contains every sufficiently narrow
discriminant-scaled interval used in Stark descent. -/
theorem rational_completedXi_nonzero_scaled
    (σ : OrderedEmbeddings 1 ℚ) :
    ∃ a : ℝ, 0 < a ∧ ∀ L : ℝ, 4 ≤ L →
      ∀ β ∈ Icc (1 - a / L) 1,
        completedThetaXi σ (by simp : Module.finrank ℚ ℚ = 1) β ≠ 0 := by
  obtain ⟨a, ha, he⟩ := rational_completedXi_nonzero_near_one σ
  refine ⟨a, ha, fun L hL β hβ => he β ⟨?_, hβ.2⟩⟩
  have hdiv : a / L ≤ a := div_le_self ha.le (by linarith)
  linarith [hβ.1]

end DukePrimeDegree

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_NormalClosure
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EmbeddingOrder.toRealOrder_apply
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
namespace PrimeDegreePackets

lemma abs_discr_le_of_algHom {K N : Type*} [Field K] [NumberField K]
    [Field N] [NumberField N] (f : K →ₐ[ℚ] N) :
    |(NumberField.discr K : ℝ)| ≤ |(NumberField.discr N : ℝ)| := by
  let : Algebra K N := f.toRingHom.toAlgebra
  have H := Int.natAbs_le_of_dvd_ne_zero (NumberField.discr_dvd_discr K N)
    (NumberField.discr_ne_zero N)
  have H' : (|(NumberField.discr K)| : ℤ) ≤ |NumberField.discr N| := by
    simpa only [Int.natCast_natAbs] using (show ((NumberField.discr K).natAbs : ℤ) ≤
      ((NumberField.discr N).natAbs : ℤ) from by exact_mod_cast H)
  exact_mod_cast H'

lemma normalClosure_abs_discr_ge {K N : Type*} [Field K] [NumberField K]
    [Field N] [NumberField N] [IsNormalClosure ℚ K N] :
    |(NumberField.discr K : ℝ)| ≤ |(NumberField.discr N : ℝ)| := by
  obtain ⟨f⟩ := IntermediateField.nonempty_algHom_of_splits
    (fun x : K => ⟨Algebra.IsIntegral.isIntegral x,
      IsNormalClosure.splits (F := ℚ) (K := K) (L := N) x⟩)
  exact abs_discr_le_of_algHom f

namespace HeckeMellin
open AnalyticGrowth



theorem normalClosure_zero_box_uniform (d : ℕ) :
    ∃ C T : ℝ, 0 < C ∧ 0 < T ∧
      ∀ {K N : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
        [Field N] [NumberField N] [IsNormalClosure ℚ K N] [NumberField.IsTotallyReal N]
        (_σ : OrderedEmbeddings (d+1) K) (_hn : finrank ℚ K = d+1)
        {m : ℕ} (τ : OrderedEmbeddings (m+1) N) (hm : finrank ℚ N = m+1),
      T < Real.log |(NumberField.discr K : ℝ)| →
      ∀ ρ, ρ ∈ dedekindXiZeros τ hm →
        InNearOneBox (C*Real.log (3*|(NumberField.discr K : ℝ)|)) ρ →
        zeroMultiplicity (completedThetaXi τ hm) ρ = 1 ∧ ρ.im = 0 ∧
          ∀ z, z ∈ dedekindXiZeros τ hm →
            InNearOneBox (C*Real.log (3*|(NumberField.discr K : ℝ)|)) z → z = ρ := by
  obtain ⟨C,hC,hdisc⟩ := normalClosure_log_discr_uniform d
  obtain ⟨T,hT,hzero⟩ := boundedDegree_near_one_zero_real_simple_unique (d+1).factorial
  refine ⟨C,T,hC,hT,?_⟩
  intro K N _ _ _ _ _ _ _ σ hn m τ hm hL ρ hρ hbox
  let : Normal ℚ N := IsNormalClosure.normal (K := K)
  let : IsGalois ℚ N := {}
  have hdim : m+1 ≤ (d+1).factorial := by
    simpa only [hm,hn] using (normalClosure_finrank_le_factorial (F := ℚ) (K := K) (N := N))
  have hDK : 0 < |(NumberField.discr K : ℝ)| :=
    abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero K)
  have hDN : 0 < |(NumberField.discr N : ℝ)| :=
    abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero N)
  have hlog : Real.log |(NumberField.discr K : ℝ)| ≤
      Real.log |(NumberField.discr N : ℝ)| :=
    Real.log_le_log hDK normalClosure_abs_discr_ge
  have hLN : 0 < Real.log |(NumberField.discr N : ℝ)| := hT.trans (hL.trans_le hlog)
  have hbound : Real.log |(NumberField.discr N : ℝ)| ≤
      C*Real.log (3*|(NumberField.discr K : ℝ)|) :=
    (Real.log_le_log hDN (by nlinarith)).trans (hdisc K N σ hn)
  have hboxes : ∀ z, InNearOneBox (C*Real.log (3*|(NumberField.discr K : ℝ)|)) z →
      InNearOneBox (Real.log |(NumberField.discr N : ℝ)|) z := by
    intro z hz
    have hi := one_div_le_one_div_of_le (mul_pos (by norm_num : (0:ℝ)<4) hLN)
      (mul_le_mul_of_nonneg_left hbound (by norm_num : (0:ℝ)≤4))
    exact ⟨by linarith [hz.1], hz.2.trans hi⟩
  obtain ⟨hs,hr,hu⟩ := hzero hdim τ hm (hL.trans_le hlog) ρ hρ (hboxes ρ hbox)
  exact ⟨hs,hr,fun z hz hb => hu z hz (hboxes z hb)⟩

end HeckeMellin
end PrimeDegreePackets


end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_CosetMeromorphic
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EmbeddingOrder.toRealOrder_apply
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



end PrimeDegreePackets.GaloisIdealCharacter

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Arithmetic_ZetaOrder
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue
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

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Arithmetic_ZetaIsomorphism
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Continued zeta orders respect field isomorphisms

The Dirichlet coefficients are preserved by a number-field isomorphism.
Uniqueness of analytic continuation therefore preserves the zero order,
including for the bottom field in a normal closure.
-/

noncomputable section
open Filter Set
open scoped NumberField Classical Topology

namespace DukePrimeDegree
open PrimeDegreePackets PrimeDegreePackets.GaloisIdealCharacter
  PrimeDegreePackets.HeckeMellin

lemma removedEulerPolynomial_one (K : Type*) [Field K] [NumberField K] (s : ℂ) :
    removedEulerPolynomial K 1 s = 1 := by
  have hbad : badRationalPrimes 1 = ∅ := by
    ext p
    change (⟨p.val, p.property⟩ : Subtype Nat.Prime) ∈
      (1 : ℕ).primeFactors.subtype Nat.Prime ↔ p ∈ (∅ : Finset Nat.Primes)
    rw [Finset.mem_subtype]
    simp
  simp only [removedEulerPolynomial, hbad, Finset.prod_empty]

theorem zetaZeroOrder_algEquiv
    {K L : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    [Field L] [NumberField L] [NumberField.IsTotallyReal L]
    (e : K ≃ₐ[ℚ] L) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    zetaZeroOrder K β = zetaZeroOrder L β := by
  let σ := canonicalRealEmbeddings K
  let τ := canonicalRealEmbeddings L
  have heq := analytic_off_zero_one_eq_of_real_eq
    (coset_analytic_off_zero_one σ (degreePred_spec K) 1)
    (coset_analytic_off_zero_one τ (degreePred_spec L) 1) (fun s hs => by
      rw [cosetMeromorphic_eq_dedekindZeta σ (degreePred_spec K) 1 hs,
        cosetMeromorphic_eq_dedekindZeta τ (degreePred_spec L) 1 hs,
        removedEulerPolynomial_one, removedEulerPolynomial_one,
        mul_one, mul_one]
      exact dedekindZeta_algEquiv e s)
  have hopen : IsOpen ({0, 1} : Set ℂ)ᶜ :=
    (Set.Finite.isClosed (by simp)).isOpen_compl
  have hβ : (β : ℂ) ∈ ({0, 1} : Set ℂ)ᶜ := by
    simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
    exact ⟨Complex.ofReal_ne_zero.mpr hβ0.ne', by exact_mod_cast hβ1.ne⟩
  apply meromorphicOrderAt_congr
  have hu : ∀ᶠ z in 𝓝 (β : ℂ), z ∈ ({0, 1} : Set ℂ)ᶜ := hopen.mem_nhds hβ
  filter_upwards [hu.filter_mono nhdsWithin_le_nhds] with z hz
  exact heq hz

theorem zetaMultiplicity_algEquiv
    {K L : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    [Field L] [NumberField L] [NumberField.IsTotallyReal L]
    (e : K ≃ₐ[ℚ] L) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    zetaMultiplicity K β = zetaMultiplicity L β := by
  unfold zetaMultiplicity
  rw [zetaZeroOrder_algEquiv e hβ0 hβ1]

theorem zetaMultiplicity_eq_zero_of_completed_ne_zero
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    {d : ℕ} (σ : OrderedEmbeddings (d + 1) K) (hn : Module.finrank ℚ K = d + 1)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hzero : completedThetaXi σ hn (β : ℂ) ≠ 0) : zetaMultiplicity K β = 0 := by
  have hord : zetaZeroOrder K β = 0 := by
    rw [zetaZeroOrder_eq_completed_order σ hn hβ0 hβ1]
    exact ((completedThetaXi_entire σ hn).analyticAt _).meromorphicNFAt
      |>.meromorphicOrderAt_eq_zero_iff.mpr hzero
  simp [zetaMultiplicity, hord]

theorem rational_zetaMultiplicity_zero_scaled :
    ∃ a : ℝ, 0 < a ∧ ∀ L : ℝ, 4 ≤ L →
      ∀ β ∈ Icc (1 - a / L) 1, 0 < β → β < 1 → zetaMultiplicity ℚ β = 0 := by
  let σ := canonicalRealEmbeddings ℚ
  have hdeg : degreePred ℚ = 0 := by simp [degreePred]
  have hσ : OrderedEmbeddings 1 ℚ := by simpa only [hdeg, Nat.zero_add] using σ
  obtain ⟨a, ha, hz⟩ := rational_completedXi_nonzero_scaled hσ
  refine ⟨a, ha, fun L hL β hβ hβ0 hβ1 => ?_⟩
  exact zetaMultiplicity_eq_zero_of_completed_ne_zero hσ (by simp)
    hβ0 hβ1 (hz L hL β hβ)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Arithmetic_FixedFieldTower
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The cyclic fixed-field tower

The automorphisms over a fixed field are the original subgroup. Passing
to a smaller subgroup in this cyclic extension preserves the actual
underlying intermediate field, so the cyclic factorization applies to
the same fixed-field zeta orders used by descent.
-/

noncomputable section
open scoped Classical NumberField

namespace DukePrimeDegree

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]

lemma fixingSubgroup_extendScalars_fixedField
    (C D : Subgroup (E ≃ₐ[F] E)) (hDC : D ≤ C) :
    (IntermediateField.extendScalars (IntermediateField.fixedField_le hDC)).fixingSubgroup =
      (D.comap C.subtype).map (IntermediateField.subgroupEquivAlgEquiv C).toMonoidHom := by
  let e := IntermediateField.subgroupEquivAlgEquiv C
  apply SetLike.ext
  intro g
  rw [Subgroup.mem_map_equiv]
  change g ∈ (IntermediateField.extendScalars
    (IntermediateField.fixedField_le hDC)).fixingSubgroup ↔ (e.symm g : E ≃ₐ[F] E) ∈ D
  have hmem (σ : E ≃ₐ[F] E) : σ ∈ D ↔
      σ ∈ (IntermediateField.fixedField D).fixingSubgroup := by
    rw [IntermediateField.fixingSubgroup_fixedField]
  rw [hmem]
  simp only [IntermediateField.mem_fixingSubgroup_iff,
    IntermediateField.mem_extendScalars]
  have he (x : E) : (e.symm g : E ≃ₐ[F] E) x = g x := by
    have h := congrArg (fun σ => σ x) (e.apply_symm_apply g)
    exact h
  simp only [he]

lemma zpowers_comap_subtype
    {G : Type*} [Group G] (C : Subgroup G) (x : C) :
    (Subgroup.zpowers (x : G)).comap C.subtype = Subgroup.zpowers x := by
  change (Subgroup.zpowers (C.subtype x)).comap C.subtype = _
  rw [← MonoidHom.map_zpowers C.subtype x,
    Subgroup.comap_map_eq_self_of_injective C.subtype_injective]

lemma fixingSubgroup_extendScalars_zpowers
    (C : Subgroup (E ≃ₐ[F] E)) (x : C) :
    (IntermediateField.extendScalars (IntermediateField.fixedField_le
      (show Subgroup.zpowers (x : E ≃ₐ[F] E) ≤ C from
        Subgroup.zpowers_le.mpr x.property))).fixingSubgroup =
      Subgroup.zpowers (IntermediateField.subgroupEquivAlgEquiv C x) := by
  rw [fixingSubgroup_extendScalars_fixedField C (Subgroup.zpowers (x : E ≃ₐ[F] E))
    (Subgroup.zpowers_le.mpr x.property), zpowers_comap_subtype,
    MonoidHom.map_zpowers]
  rfl

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Arithmetic_CyclicFixedOrders
attribute [-instance] _root_.AlgebraicNumberTheory.numberFieldInRationalSeparableClosure_numberField _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateFieldAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateFieldNumberField _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionField_isGalois _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueExtension_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.finiteNormalClosure_numberField _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Cyclic characters on the Galois group of a normal closure

The cyclic factorization over the fixed field of a subgroup gives a
character on that subgroup. The tower identification relates its values
to the original fixed-field zero multiplicities, as required for gluing.
-/

noncomputable section
open scoped NumberField Classical

namespace DukePrimeDegree
open PrimeDegreePackets PrimeDegreePackets.GaloisIdealCharacter

variable {E : Type*} [Field E] [NumberField E] [IsGalois ℚ E]
variable [NumberField.IsTotallyReal E]
variable (C : Subgroup (E ≃ₐ[ℚ] E)) [IsCyclic C]
local instance instIsCyclicAlgEquivSubtypeMemIntermediateFieldRatFixedField_solutions : IsCyclic (E ≃ₐ[IntermediateField.fixedField C] E) :=
  (IntermediateField.subgroupEquivAlgEquiv C).isCyclic.mp inferInstance
local instance instIsTotallyRealSubtypeMemIntermediateFieldRatFixedField_solutions : NumberField.IsTotallyReal (IntermediateField.fixedField C) :=
  NumberField.IsTotallyReal.of_algebra _ E
local instance instIsTotallyRealSubtypeMemIntermediateFieldRatFixedField_solutions_1 (L : IntermediateField (IntermediateField.fixedField C) E) :
    NumberField.IsTotallyReal L := NumberField.IsTotallyReal.of_algebra _ E

/-- A simple normal-closure zero gives the cyclic sign data directly in
terms of the original subgroup lattice. -/
theorem cyclic_fixedField_character
    {N : ℕ} [NeZero N]
    (ψ : ((E ≃ₐ[IntermediateField.fixedField C] E) →* ℂˣ) →
      EvenRayCharacter (IntermediateField.fixedField C) N)
    (hid : ∀ χ, (ψ χ).idealHom = idealHom (IntermediateField.fixedField C) E χ)
    (hψ : ∀ χ, χ ≠ 1 → (ψ χ).IsNonprincipal)
    (hD : (NumberField.discr E).natAbs ∣ N)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hsimple : zetaMultiplicity E β = 1) :
    ∃ χ : C →* ℝˣ,
      (∀ x : C, fixedFieldMultiplicity β (Subgroup.zpowers (x : E ≃ₐ[ℚ] E)) =
        if χ x = 1 then 1 else 0) ∧
      fixedFieldMultiplicity β C = if χ = 1 then 1 else 0 := by
  obtain ⟨χ, hχ⟩ := exists_real_character_of_simple_zeta ψ hid hψ hD hβ0 hβ1 hsimple
  let e := IntermediateField.subgroupEquivAlgEquiv C
  let χC : C →* ℝˣ := χ.comp e.toMonoidHom
  refine ⟨χC, ?_, ?_⟩
  · intro x
    let L := IntermediateField.extendScalars (IntermediateField.fixedField_le
      (show Subgroup.zpowers (x : E ≃ₐ[ℚ] E) ≤ C from Subgroup.zpowers_le.mpr x.property))
    have hx := hχ L
    rw [fixingSubgroup_extendScalars_zpowers, Subgroup.zpowers_le] at hx
    let D := IntermediateField.fixedField (Subgroup.zpowers (x : E ≃ₐ[ℚ] E))
    let eL : L ≃ₐ[ℚ] D :=
      { toFun := fun z => ⟨z.val, z.property⟩
        invFun := fun z => ⟨z.val, z.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_mul' := fun _ _ => rfl
        map_add' := fun _ _ => rfl
        commutes' := fun _ => rfl }
    have hz := zetaMultiplicity_algEquiv eL hβ0 hβ1
    rw [hz] at hx
    by_cases hcx : χ (e x) = 1
    · simpa only [fixedFieldMultiplicity, MonoidHom.mem_ker, χC, MonoidHom.comp_apply,
        MulEquiv.coe_toMonoidHom, e, D, hcx, ite_true, if_true] using hx
    · simpa only [fixedFieldMultiplicity, MonoidHom.mem_ker, χC, MonoidHom.comp_apply,
        MulEquiv.coe_toMonoidHom, e, D, hcx, ite_false, if_false] using hx
  · have hcomp : χC = 1 ↔ χ = 1 := by
      constructor
      · intro h
        apply MonoidHom.ext
        intro g
        obtain ⟨x, rfl⟩ := e.surjective g
        exact DFunLike.congr_fun h x
      · rintro rfl
        rfl
    have hbot := hχ (⊥ : IntermediateField (IntermediateField.fixedField C) E)
    have hbase := zetaMultiplicity_algEquiv
      ((IntermediateField.botEquiv (IntermediateField.fixedField C) E).restrictScalars ℚ)
      hβ0 hβ1
    rw [hbase, IntermediateField.fixingSubgroup_bot, top_le_iff,
      MonoidHom.ker_eq_top_iff, ← hcomp] at hbot
    by_cases hprincipal : χC = 1
    · simpa only [fixedFieldMultiplicity, hprincipal, ite_true, if_true] using hbot
    · simpa only [fixedFieldMultiplicity, hprincipal, ite_false, if_false] using hbot

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Arithmetic_StarkDescent
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Odd-index descent of a simple zero

Cyclic Hecke factorizations supply the real characters used by Stark's
odd-degree argument. The zero order on any fixed field is an average of
signs and is therefore at most one. A positive order at an odd-index
subgroup is incompatible with a nonvanishing rational zeta function.
-/

noncomputable section
open scoped NumberField BigOperators Classical

namespace DukePrimeDegree
open PrimeDegreePackets PrimeDegreePackets.GaloisIdealCharacter

variable {E : Type*} [Field E] [NumberField E] [IsGalois ℚ E]
variable [NumberField.IsTotallyReal E]

attribute [local instance] OAI.DukePrimeDegree.starkDescentFintype
theorem cyclic_character_of_ray_realizations
    (hray : HasCyclicRayRealizations E)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hsimple : zetaMultiplicity E β = 1)
    (C : Subgroup (E ≃ₐ[ℚ] E)) (hC : IsCyclic C) :
    ∃ χ : C →* ℝˣ,
      (∀ x : C, fixedFieldMultiplicity β (Subgroup.zpowers (x : E ≃ₐ[ℚ] E)) =
        if χ x = 1 then 1 else 0) ∧
      fixedFieldMultiplicity β C = if χ = 1 then 1 else 0 := by
  let := hC
  obtain ⟨N, hN, hD, ψ, hid, hψ⟩ := hray C hC
  let : NeZero N := ⟨hN.ne'⟩
  obtain ⟨χ, hχ, hp⟩ := cyclic_fixedField_character
    (E := E) (N := N) (β := β) C ψ hid hψ hD hβ0 hβ1 hsimple
  refine ⟨χ, ?_, ?_⟩
  · intro x
    by_cases hx : χ x = 1
    · simpa only [hx, ite_true, if_true] using hχ x
    · simpa only [hx, ite_false, if_false] using hχ x
  · by_cases hx : χ = 1
    · simpa only [hx, ite_true, if_true] using hp
    · simpa only [hx, ite_false, if_false] using hp

/-- The final finite Galois descent, before choosing a normal closure. -/
theorem no_odd_index_zero_of_ray_realizations
    (hray : HasCyclicRayRealizations E)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hsimple : zetaMultiplicity E β = 1)
    (H : Subgroup (E ≃ₐ[ℚ] E)) (hodd : Odd H.index)
    (hH : 0 < fixedFieldMultiplicity β H) (hQ : zetaMultiplicity ℚ β = 0) : False := by
  exact no_odd_index_positive_zero_of_cyclic_characters hβ0 hβ1
    (cyclic_character_of_ray_realizations hray hβ0 hβ1 hsimple) H hodd hH hQ

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Arithmetic_StarkScale
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The normal-closure simple-zero scale

The discriminant and zero-box bounds provide a fixed positive
scale, depending only on the degree, on which a normal-closure zero is
simple. This converts that statement to the integer multiplicities used
by the descent argument.
-/

noncomputable section
open Module Set
open scoped NumberField Classical

namespace DukePrimeDegree
open PrimeDegreePackets PrimeDegreePackets.HeckeMellin PrimeDegreePackets.AnalyticGrowth

theorem zetaMultiplicity_eq_zeroMultiplicity
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    {d : ℕ} (σ : OrderedEmbeddings (d + 1) K) (hn : finrank ℚ K = d + 1)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    zetaMultiplicity K β = zeroMultiplicity (completedThetaXi σ hn) (β : ℂ) := by
  unfold zetaMultiplicity zeroMultiplicity
  rw [zetaZeroOrder_eq_completed_order σ hn hβ0 hβ1]
  rfl

lemma real_mem_scaled_normalClosure_box
    {D C a β : ℝ} (hD : 0 < D) (hL : 4 ≤ Real.log D) (hC : 0 < C)
    (ha : a ≤ 1 / (8 * C)) (hβ : 1 - a / Real.log D ≤ β) :
    InNearOneBox (C * Real.log (3 * D)) (β : ℂ) := by
  have hLp : 0 < Real.log D := by linarith
  have hlog3 : Real.log 3 ≤ 2 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num)
    linarith
  have hlog : Real.log (3 * D) = Real.log 3 + Real.log D :=
    Real.log_mul (by norm_num) hD.ne'
  have hlogp : 0 < Real.log (3 * D) := by
    rw [hlog]
    have : 0 < Real.log 3 := Real.log_pos (by norm_num)
    linarith
  have hb : Real.log (3 * D) ≤ 2 * Real.log D := by rw [hlog]; linarith
  have hden : 4 * (C * Real.log (3 * D)) ≤ 8 * C * Real.log D := by nlinarith
  have hfrac := one_div_le_one_div_of_le
    (show 0 < 4 * (C * Real.log (3 * D)) by positivity) hden
  have haL : a / Real.log D ≤ 1 / (8 * C * Real.log D) := by
    calc
      a / Real.log D ≤ (1 / (8 * C)) / Real.log D := div_le_div_of_nonneg_right ha hLp.le
      _ = 1 / (8 * C * Real.log D) := by rw [div_div]
  constructor
  · change 1 - 1 / (4 * (C * Real.log (3 * D))) ≤ β
    linarith
  · change |(0 : ℝ)| ≤ 1 / (4 * (C * Real.log (3 * D)))
    rw [abs_zero]
    positivity

theorem normalClosure_simple_zero_scaled (d : ℕ) :
    ∃ a T : ℝ, 0 < a ∧ a ≤ 1 ∧ 4 ≤ T ∧
      ∀ {K E : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
        [Field E] [NumberField E] [IsNormalClosure ℚ K E] [NumberField.IsTotallyReal E]
        (_σ : OrderedEmbeddings (d + 1) K) (_hn : finrank ℚ K = d + 1),
        T ≤ Real.log |(NumberField.discr K : ℝ)| →
        ∀ β : ℝ, 0 < β → β < 1 →
          1 - a / Real.log |(NumberField.discr K : ℝ)| ≤ β →
          zetaMultiplicity E β ≠ 0 → zetaMultiplicity E β = 1 := by
  obtain ⟨C, T, hC, hT, hzero⟩ := normalClosure_zero_box_uniform d
  refine ⟨min 1 (1 / (8 * C)), max 4 (T + 1), by positivity, min_le_left _ _,
    le_max_left _ _, ?_⟩
  intro K E _ _ _ _ _ _ _ σ hn hL β hβ0 hβ1 hβ hne
  let τ := canonicalRealEmbeddings E
  have he := degreePred_spec E
  have hord := zetaMultiplicity_eq_zeroMultiplicity τ he hβ0 hβ1
  have hEzero : completedThetaXi τ he (β : ℂ) = 0 := by
    apply (zeroMultiplicity_ne_zero_iff (completedThetaXi_entire τ he)
      (dedekindXiZeros_ne_zero_totallyReal τ he) (β : ℂ)).mp
    rwa [← hord]
  have hthreshold : T < Real.log |(NumberField.discr K : ℝ)| := by
    have := le_max_right 4 (T + 1)
    linarith
  have hbox := real_mem_scaled_normalClosure_box
    (abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero K))
    ((le_max_left 4 (T + 1)).trans hL) hC (min_le_right _ _) hβ
  exact hord.trans (hzero σ hn τ he hthreshold (β : ℂ) hEzero hbox).1

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Arithmetic_StarkNormalClosure
attribute [-instance] _root_.AlgebraicNumberTheory.numberFieldInRationalSeparableClosure_numberField _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateFieldAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateFieldNumberField _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalClassFieldTheory.finiteGaloisFieldRangeOfEmbedding_finiteDimensional _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueExtension_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.finiteNormalClosure_numberField _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Assembling the normal-closure argument

Realizing cyclic Frobenius characters by even ray characters gives
zero propagation to the normal closure. Simplicity near one and
odd-index descent then exclude an exceptional real zero.
-/

noncomputable section
open Module Set IntermediateField
open scoped NumberField Classical

namespace DukePrimeDegree
open PrimeDegreePackets PrimeDegreePackets.HeckeMellin PrimeDegreePackets.AnalyticGrowth

universe u

lemma fixedFieldMultiplicity_fixingSubgroup
    {K E : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    [Field E] [NumberField E] [NumberField.IsTotallyReal E] [IsGalois ℚ E]
    (f : K →ₐ[ℚ] E) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    fixedFieldMultiplicity β f.fieldRange.fixingSubgroup = zetaMultiplicity K β := by
  let L := f.fieldRange
  let e : IntermediateField.fixedField L.fixingSubgroup ≃ₐ[ℚ] L :=
    IntermediateField.equivOfEq (IsGalois.fixedField_fixingSubgroup L)
  exact (zetaMultiplicity_algEquiv e hβ0 hβ1).trans
    (zetaMultiplicity_algEquiv f.equivFieldRange hβ0 hβ1).symm

lemma fixingSubgroup_index_of_embedding
    {K E : Type*} [Field K] [NumberField K] [Field E] [NumberField E]
    [IsGalois ℚ E] (f : K →ₐ[ℚ] E) :
    f.fieldRange.fixingSubgroup.index = finrank ℚ K := by
  rw [← IntermediateField.finrank_eq_fixingSubgroup_index]
  exact f.equivFieldRange.toLinearEquiv.finrank_eq.symm

/-- The zero-exclusion consequence of cyclic reciprocity, for the exact
family of normal closures required by the application. -/
theorem exceptionalRealZeroExclusion_of_ray_realizations_oai
    (d : ℕ) (hodd : Odd (d + 1))
    (hray : ∀ (E : Type u) [Field E] [NumberField E] [IsGalois ℚ E]
      [NumberField.IsTotallyReal E], HasCyclicRayRealizations E) :
    ExceptionalRealZeroExclusion.{u} d := by
  obtain ⟨a, T, ha, ha1, hT, hsimple⟩ := normalClosure_simple_zero_scaled d
  obtain ⟨b, hb, hQ⟩ := rational_zetaMultiplicity_zero_scaled
  refine ⟨min a b, T, lt_min ha hb, hT, ?_⟩
  intro K _ _ _ hn σ hL β hβ hβ1 hzero
  have hLp : 0 < Real.log |(NumberField.discr K : ℝ)| := lt_of_lt_of_le (by linarith) hL
  have hfrac : min a b / Real.log |(NumberField.discr K : ℝ)| ≤ 1 / 4 := by
    have ha' : min a b ≤ 1 := (min_le_left _ _).trans ha1
    apply (div_le_iff₀ hLp).mpr
    have hL4 := hT.trans hL
    nlinarith
  have hβ0 : 0 < β := by linarith
  let E := normalClosure ℚ K (AlgebraicClosure K)
  let : Algebra.IsAlgebraic ℚ (AlgebraicClosure K) := Algebra.IsAlgebraic.trans ℚ K _
  let : IsAlgClosure ℚ (AlgebraicClosure K) := ⟨inferInstance, inferInstance⟩
  let : Nonempty (K →ₐ[ℚ] AlgebraicClosure K) := ⟨IsScalarTower.toAlgHom ℚ K _⟩
  let : IsNormalClosure ℚ K E := isNormalClosure_normalClosure ℚ K (AlgebraicClosure K)
  let : Normal ℚ E := IsNormalClosure.normal (K := K)
  let : IsGalois ℚ E := {}
  let : NumberField E := {}
  let : NumberField.IsTotallyReal E := normalClosure_isTotallyReal
  obtain ⟨f⟩ := IntermediateField.nonempty_algHom_of_splits
    (fun x : K => ⟨Algebra.IsIntegral.isIntegral x,
      IsNormalClosure.splits (F := ℚ) (K := K) (L := E) x⟩)
  let H := f.fieldRange.fixingSubgroup
  have hHodd : Odd H.index := by
    rw [fixingSubgroup_index_of_embedding f, hn]
    exact hodd
  have hKpos : 0 < zetaMultiplicity K β := by
    rw [zetaMultiplicity_eq_zeroMultiplicity σ hn hβ0 hβ1]
    exact lt_of_le_of_ne (zeroMultiplicity_nonneg (completedThetaXi_entire σ hn) _)
      (Ne.symm ((zeroMultiplicity_ne_zero_iff (completedThetaXi_entire σ hn)
        (dedekindXiZeros_ne_zero_totallyReal σ hn) (β : ℂ)).mpr hzero))
  have hHpos : 0 < fixedFieldMultiplicity β H := by
    rw [fixedFieldMultiplicity_fixingSubgroup f hβ0 hβ1]
    exact hKpos
  have hEpos := extension_multiplicity_pos_of_ray_realizations (hray E) hβ0 hβ1 H hHpos
  have hβa : 1 - a / Real.log |(NumberField.discr K : ℝ)| ≤ β := by
    have hh := div_le_div_of_nonneg_right (min_le_left a b) hLp.le
    linarith
  have hEone := hsimple σ hn hL β hβ0 hβ1 hβa (ne_of_gt hEpos)
  have hβb : 1 - b / Real.log |(NumberField.discr K : ℝ)| ≤ β := by
    have hh := div_le_div_of_nonneg_right (min_le_right a b) hLp.le
    linarith
  exact no_odd_index_zero_of_ray_realizations (hray E) hβ0 hβ1 hEone H hHodd hHpos
    (hQ _ (hT.trans hL) β ⟨hβb, hβ1.le⟩ hβ0 hβ1)

end DukePrimeDegree

end

end OAI
end

theorem solution.{u} : type_of% @OAI.DukePrimeDegree.exceptionalRealZeroExclusion_of_ray_realizations_oai.{u} := @OAI.DukePrimeDegree.exceptionalRealZeroExclusion_of_ray_realizations_oai.{u}
