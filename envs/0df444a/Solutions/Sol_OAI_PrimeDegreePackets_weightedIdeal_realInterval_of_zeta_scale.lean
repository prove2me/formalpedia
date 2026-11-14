-- Prove2me | solution 1 for OAI.PrimeDegreePackets.weightedIdeal_realInterval_of_zeta_scale
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T06:55:13.516781+00:00
-- url     : https://prove2.me/submissions/01c5018c-d63a-44d2-9afe-6ade2e345087

import Mathlib
import Definitions.Def_DukePrimeDegree
import Definitions.Def_OAIQ244Duke036
import Theorems.Thm_OAI_PrimeDegreePackets_primaryIdeal_reciprocal_tail
import Theorems.Thm_OAI_PrimeDegreePackets_weightedIdeal_small_norm_bound

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_DivisorBounds
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
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
namespace PrimeDegreePackets

 

lemma sum_divisors_initial {A : Type*} [AddCommMonoid A] (F : ℕ → ℕ → A) (N : ℕ) :
    (∑ m ∈ Icc 1 N, ∑ d ∈ m.divisors, F d (m / d)) =
      ∑ d ∈ Icc 1 N, ∑ e ∈ Icc 1 (N / d), F d e := by
  classical
  rw [sum_sigma', sum_sigma']
  apply sum_bij (fun p _ => ⟨p.2, p.1 / p.2⟩)
  · intro p hp
    obtain ⟨hm, hd⟩ := mem_sigma.mp hp
    obtain ⟨hdm, hm0⟩ := Nat.mem_divisors.mp hd
    have hd0 := Nat.pos_of_mem_divisors hd
    have hdmle := Nat.le_of_dvd (by omega : 0 < p.1) hdm
    apply mem_sigma.mpr
    refine ⟨mem_Icc.mpr ⟨hd0, hdmle.trans (mem_Icc.mp hm).2⟩, mem_Icc.mpr ⟨?_, ?_⟩⟩
    · exact Nat.le_div_iff_mul_le hd0 |>.mpr (by simpa using hdmle)
    · exact Nat.div_le_div_right (mem_Icc.mp hm).2
  · intro p hp q hq hpq
    obtain ⟨hpm, hpd⟩ := mem_sigma.mp hp
    obtain ⟨hqm, hqd⟩ := mem_sigma.mp hq
    have h1 : p.2 = q.2 := congrArg Sigma.fst hpq
    have h2 : p.1 / p.2 = q.1 / q.2 := by simpa using congrArg Sigma.snd hpq
    have hm : p.1 = q.1 := by
      calc
        p.1 = p.2 * (p.1 / p.2) := (Nat.mul_div_cancel' (Nat.mem_divisors.mp hpd).1).symm
        _ = q.2 * (q.1 / q.2) := by rw [h2, h1]
        _ = q.1 := Nat.mul_div_cancel' (Nat.mem_divisors.mp hqd).1
    cases p
    cases q
    simp_all
  · intro q hq
    obtain ⟨hd, he⟩ := mem_sigma.mp hq
    have hd0 : 0 < q.1 := (mem_Icc.mp hd).1
    have he0 : 0 < q.2 := (mem_Icc.mp he).1
    have hmul : q.1 * q.2 ≤ N := by
      simpa [mul_comm] using (Nat.le_div_iff_mul_le hd0).mp (mem_Icc.mp he).2
    refine ⟨⟨q.1 * q.2, q.1⟩, mem_sigma.mpr ⟨mem_Icc.mpr ⟨Nat.mul_pos hd0 he0, hmul⟩,
      Nat.mem_divisors.mpr ⟨dvd_mul_right _ _, by positivity⟩⟩, ?_⟩
    simp [Nat.mul_div_cancel_left _ hd0]
  · intro p hp
    rfl



lemma nFoldDivisor_succ (k m : ℕ) :
    nFoldDivisor (k + 1) m = ∑ d ∈ m.divisors, nFoldDivisor k d := by
  simp only [nFoldDivisor, pow_succ, ArithmeticFunction.mul_zeta_apply]

lemma nFoldDivisor_one (m : ℕ) : nFoldDivisor 1 m = if m = 0 then 0 else 1 := by
  simp only [nFoldDivisor, pow_one]
  rfl

 
lemma nFoldDivisor_sum_succ (k N : ℕ) :
    (∑ m ∈ Icc 1 N, nFoldDivisor (k + 1) m) =
      ∑ d ∈ Icc 1 N, nFoldDivisor k d * (N / d) := by
  simp_rw [nFoldDivisor_succ]
  rw [sum_divisors_initial (fun d _ => nFoldDivisor k d)]
  simp [Nat.card_Icc, mul_comm]

lemma harmonic_real_eq_sum (N : ℕ) :
    (harmonic N : ℝ) = ∑ d ∈ Icc 1 N, (d : ℝ)⁻¹ := by
  simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]

lemma harmonic_real_nonneg (N : ℕ) : 0 ≤ (harmonic N : ℝ) := by
  rw [harmonic_real_eq_sum]
  exact Finset.sum_nonneg (fun _ _ => by positivity)

lemma harmonic_real_mono {M N : ℕ} (h : M ≤ N) :
    (harmonic M : ℝ) ≤ harmonic N := by
  simp only [harmonic_real_eq_sum]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right h)
    (fun _ _ _ => by positivity)

 

lemma nFoldDivisor_reciprocal_sum (k N : ℕ) :
    (∑ m ∈ Icc 1 N, (nFoldDivisor k m : ℝ) / m) ≤ (harmonic N : ℝ) ^ k := by
  induction k with
  | zero =>
    simp only [nFoldDivisor, pow_zero, ArithmeticFunction.one_apply]
    by_cases hN : 1 ≤ N
    · simp [ite_div, hN]
    · have : N = 0 := by omega
      simp [this]
  | succ k ih =>
    have hc : (∑ m ∈ Icc 1 N, (nFoldDivisor (k + 1) m : ℝ) / m) =
        ∑ d ∈ Icc 1 N, ∑ e ∈ Icc 1 (N / d), (nFoldDivisor k d : ℝ) / (d * e) := by
      simp_rw [nFoldDivisor_succ, Nat.cast_sum, Finset.sum_div]
      have hid := sum_divisors_initial (fun d e => (nFoldDivisor k d : ℝ) / (d * e)) N
      convert hid using 1
      all_goals try with_reducible_and_instances rfl
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_congr rfl
      intro d hd
      rw [← Nat.cast_mul, Nat.mul_div_cancel' (Nat.mem_divisors.mp hd).1]
    rw [hc]
    calc
      _ = ∑ d ∈ Icc 1 N, ((nFoldDivisor k d : ℝ) / d) * harmonic (N / d) := by
        apply Finset.sum_congr rfl
        intro d hd
        rw [harmonic_real_eq_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro e he
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
      _ ≤ ∑ d ∈ Icc 1 N, ((nFoldDivisor k d : ℝ) / d) * harmonic N := by
        apply Finset.sum_le_sum
        intro d hd
        exact mul_le_mul_of_nonneg_left (harmonic_real_mono (Nat.div_le_self _ _)) (by positivity)
      _ = (∑ d ∈ Icc 1 N, (nFoldDivisor k d : ℝ) / d) * harmonic N := by rw [Finset.sum_mul]
      _ ≤ (harmonic N : ℝ) ^ k * harmonic N :=
        mul_le_mul_of_nonneg_right ih (harmonic_real_nonneg N)
      _ = (harmonic N : ℝ) ^ (k + 1) := (pow_succ _ _).symm

 

theorem nFoldDivisor_summatory_le (k N : ℕ) :
    (∑ m ∈ Icc 1 N, (nFoldDivisor (k + 1) m : ℝ)) ≤
      N * (1 + Real.log N) ^ k := by
  have hsum : (∑ m ∈ Icc 1 N, (nFoldDivisor (k + 1) m : ℝ)) =
      ∑ d ∈ Icc 1 N, (nFoldDivisor k d : ℝ) * (N / d : ℕ) := by
    exact_mod_cast nFoldDivisor_sum_succ k N
  rw [hsum]
  calc
    _ ≤ ∑ d ∈ Icc 1 N, (nFoldDivisor k d : ℝ) * ((N : ℝ) / d) := by
      apply Finset.sum_le_sum
      intro d hd
      exact mul_le_mul_of_nonneg_left ((Nat.cast_div_le)) (by positivity)
    _ = (N : ℝ) * ∑ d ∈ Icc 1 N, (nFoldDivisor k d : ℝ) / d := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      ring
    _ ≤ (N : ℝ) * (harmonic N : ℝ) ^ k :=
      mul_le_mul_of_nonneg_left (nFoldDivisor_reciprocal_sum k N) (by positivity)
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact pow_le_pow_left₀ (harmonic_real_nonneg N) (harmonic_le_one_add_log N) k



theorem nFoldDivisor_prime_pow (k j p : ℕ) (hp : p.Prime) :
    nFoldDivisor (k + 1) (p ^ j) = (j + k).choose k := by
  induction k generalizing j with
  | zero => simp [nFoldDivisor_one, hp.ne_zero]
  | succ k ih =>
    rw [nFoldDivisor_succ, Nat.sum_divisors_prime_pow hp]
    simp_rw [ih]
    simpa [Nat.add_assoc] using Nat.sum_range_add_choose j k


end PrimeDegreePackets


end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_PacketAlgebra
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.globalLabelsMulAction _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.model_units_measurableSpace _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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
namespace PrimeDegreePackets

open scoped NumberField Pointwise nonZeroDivisors
open NumberField


open Topology
open scoped Pointwise

open Polynomial



open scoped NNReal

open Polynomial
open scoped BigOperators

open IsDiscreteValuationRing IsLocalRing Module


open MeasureTheory
open scoped ENNReal

lemma haar_smul_containment {G A : Type*} [Group G] [MulAction G A]
    [MeasurableSpace G] [MeasurableMul G]
    (μ : Measure G) [μ.IsMulLeftInvariant] (L : Set A) (u : G) (x : A) :
    μ {z : G | u • x ∈ z • L} = μ {z : G | x ∈ z • L} := by
  have he : {z : G | u • x ∈ z • L} =
      (fun z : G => u⁻¹ * z) ⁻¹' {z : G | x ∈ z • L} := by
    ext z
    simp only [Set.mem_preimage,Set.mem_ofPred_eq,Set.mem_smul_set_iff_inv_smul_mem,
      mul_inv_rev,inv_inv,mul_smul]
  rw [he,measure_preimage_mul]

 
lemma local_generators_associated {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] (u v : (LocalAlgebra p K)ˣ)
    (h : (u : LocalAlgebra p K) • (completedMaximalOrder (K := K) p).toSubmodule =
      (v : LocalAlgebra p K) • (completedMaximalOrder (K := K) p).toSubmodule) :
    ∃ z : (completedMaximalOrder (K := K) p)ˣ,
      (u : LocalAlgebra p K) =
        ((z : completedMaximalOrder (K := K) p) : LocalAlgebra p K) * v := by
  have hr : ((v⁻¹*u : (LocalAlgebra p K)ˣ) : LocalAlgebra p K) •
      (completedMaximalOrder (K := K) p).toSubmodule =
        (completedMaximalOrder (K := K) p).toSubmodule := by
    rw [Units.val_mul,← smul_smul,h,smul_smul,Units.inv_mul,one_smul]
  obtain ⟨z,hz⟩ := completedMaximalOrder_unit_of_smul_eq p (v⁻¹*u) hr
  refine ⟨z,?_⟩
  rw [hz,Units.val_mul,mul_right_comm,Units.inv_mul,one_mul]

lemma localIdealWeight_eq_of_generator {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (p : ℕ) [Fact p.Prime]
    (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (u : (LocalAlgebra p K)ˣ)
    (hu : completedFractionalIdeal p (J : FractionalIdeal (𝓞 K)⁰ K) =
      (u : LocalAlgebra p K) • (completedMaximalOrder (K := K) p).toSubmodule) :
    localIdealWeight M p J =
      localUnitHaarProbability p {z : (completedMaximalOrder (K := K) p)ˣ |
        (u : LocalAlgebra p K) ∈
          ((z : completedMaximalOrder (K := K) p) : LocalAlgebra p K) • normalizedLocalModule M p} := by
  obtain ⟨v,hv⟩ := local_generators_associated p (idealLocalGenerator p J) u
    ((idealLocalGenerator_spec p J).symm.trans hu)
  unfold localIdealWeight
  rw [hv]
  exact haar_smul_containment (localUnitHaarProbability p)
    (normalizedLocalModule M p : Set (LocalAlgebra p K)) v u


end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_PrimeFactors
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


namespace PrimeDegreePackets
open MeasureTheory Set IsDiscreteValuationRing
open scoped ENNReal BigOperators


lemma localProductConstant_pos (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    0 < localProductConstant n ε hε :=
  (localMajorant_product_le n ε hε).choose_spec.1

end PrimeDegreePackets


end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_LocalModels
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.globalLabelsMulAction _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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
open MeasureTheory Set IsDiscreteValuationRing
open scoped ENNReal BigOperators



end PrimeDegreePackets


namespace PrimeDegreePackets
open NumberField
open scoped BigOperators Pointwise NumberField nonZeroDivisors ENNReal


lemma localIdealWeight_eq_of_completion_eq {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (p : ℕ) [Fact p.Prime]
    (I J : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (h : completedFractionalIdeal p (I : FractionalIdeal (𝓞 K)⁰ K) =
      completedFractionalIdeal p (J : FractionalIdeal (𝓞 K)⁰ K)) :
    localIdealWeight M p I = localIdealWeight M p J := by
  exact localIdealWeight_eq_of_generator M p I (idealLocalGenerator p J)
    (h.trans (idealLocalGenerator_spec p J))


end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_IdealSupport
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.globalLabelsMulAction _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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


namespace PrimeDegreePackets
open NumberField
open scoped BigOperators Pointwise NumberField nonZeroDivisors ENNReal


lemma nonzeroIntegralIdealUnit_mul {K : Type*} [Field K] [NumberField K]
    (I J : {I : Ideal (𝓞 K) // I ≠ ⊥}) :
    nonzeroIntegralIdealUnit ⟨I.1*J.1,mul_ne_zero I.2 J.2⟩ =
      nonzeroIntegralIdealUnit I * nonzeroIntegralIdealUnit J := by
  apply Units.ext
  exact FractionalIdeal.coeIdeal_mul I.1 J.1

lemma completed_ideal_mul_off {K : Type*} [Field K] [NumberField K]
    (I J : {I : Ideal (𝓞 K) // I ≠ ⊥}) (p : ℕ) [Fact p.Prime]
    (hJ : ¬ p ∣ Ideal.absNorm J.1) :
    completedFractionalIdeal p ((nonzeroIntegralIdealUnit I * nonzeroIntegralIdealUnit J :
      (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) =
      completedFractionalIdeal p (nonzeroIntegralIdealUnit I : FractionalIdeal (𝓞 K)⁰ K) := by
  rw [Units.val_mul,completedFractionalIdeal_mul,completed_ideal_eq_off J p hJ]
  rw [← completedFractionalIdeal_mul,mul_one]

lemma globalIdealWeight_mul_coprime {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (I : {I : Ideal (𝓞 K) // I ≠ ⊥})
    (J : coprimeIntegralIdeals K (saturationIndex M).primeFactors) :
    globalIdealWeight M (nonzeroIntegralIdealUnit ⟨I.1*J.1.1,mul_ne_zero I.2 J.1.2⟩) =
      globalIdealWeight M (nonzeroIntegralIdealUnit I) := by
  rw [nonzeroIntegralIdealUnit_mul]
  apply Finset.prod_congr rfl
  intro p _
  exact localIdealWeight_eq_of_completion_eq M p.val _ _ (completed_ideal_mul_off I J.1 p.val (J.2 p.val p.2))

 

theorem weighted_ideal_convolution {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (F : ℕ → ℝ≥0∞) :
    (∑' A : {I : Ideal (𝓞 K) // I ≠ ⊥},
      globalIdealWeight M (nonzeroIntegralIdealUnit A) * F (Ideal.absNorm A.1)) =
      ∑' I : primaryIntegralIdeals K (saturationIndex M).primeFactors,
        globalIdealWeight M (nonzeroIntegralIdealUnit I.1) *
          ∑' J : coprimeIntegralIdeals K (saturationIndex M).primeFactors,
            F (Ideal.absNorm I.1.1 * Ideal.absNorm J.1.1) := by
  classical
  rw [← (idealSupportEquiv (saturationIndex M).primeFactors
    (fun p hp => (Nat.mem_primeFactors.mp hp).1)).tsum_eq]
  rw [ENNReal.tsum_prod']
  apply tsum_congr
  intro I
  rw [← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro J
  change globalIdealWeight M (nonzeroIntegralIdealUnit ⟨I.1.1*J.1.1,_⟩) * F (Ideal.absNorm (I.1.1*J.1.1)) = _
  rw [globalIdealWeight_mul_coprime, map_mul]

end PrimeDegreePackets


end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_IdealCoefficients
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.finite_nsmulAddKernel_padicInt_pi _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_multiplicative_nthPowerKernel _root_.LocalFieldTheory.finite_nsmulAddKernel_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.OAI.PrimeDegreePackets.primaryIdealMultisetEquiv_val _root_.OAI.PrimeDegreePackets.primaryIdealNormEquiv_val _root_.infinitePlace_mult_smul
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


lemma ideal_factor_count_le {I : Ideal (𝓞 K)} {p r : ℕ}
    (hp : p.Prime) (hI : Ideal.absNorm I = p^r) : (normalizedFactors I).card ≤ r := by
  have hI0 : I ≠ ⊥ := by
    intro h; have H : (0:ℕ) = p^r := by simpa [h] using hI
    exact (pow_ne_zero _ hp.ne_zero) H.symm
  have H : p ^ (normalizedFactors I).card ≤ Ideal.absNorm I := by
    have H := Multiset.pow_card_le_prod (s := (normalizedFactors I).map Ideal.absNorm)
      (a := p) (by
        intro x hx
        obtain ⟨P,hP,rfl⟩ := Multiset.mem_map.mp hx
        exact (ideal_factor_prime_power K hp hI hP).2)
    simpa only [Multiset.card_map, ← map_multiset_prod, Ideal.prod_normalizedFactors_eq_self hI0] using H
  rw [hI] at H
  exact (pow_le_pow_iff_right₀ hp.one_lt).mp H


lemma idealsOverPrime_card_le {p : ℕ} (hp : p.Prime) :
    (idealsOverPrime K p).card ≤ Module.finrank ℤ (𝓞 K) := by
  exact (Multiset.toFinset_card_le _).trans
    (ideal_factor_count_le K hp (Ideal.absNorm_span_natCast p))


lemma decode_padMultiset {α : Type*} (s : Finset α) (r : ℕ) (m : Multiset α)
    (hm : ∀x ∈ m, x ∈ s) (hr : m.card ≤ r) :
    (padMultiset s r m hm hr).val.filterMap (Option.map Subtype.val) = m := by
  simp only [padMultiset, Multiset.filterMap_add, Multiset.filterMap_map]
  have hnone : ∀k, (Multiset.replicate k (none : Option s)).filterMap
      (Option.map Subtype.val) = 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [Multiset.replicate_succ, Multiset.filterMap_cons_none _ _ rfl, ih]
  rw [hnone, add_zero]
  change m.attach.filterMap (some ∘ Subtype.val) = m
  rw [Multiset.filterMap_eq_map, Multiset.attach_map_val]

lemma card_le_of_multiset_encoding {α β : Type*} (s : Finset β) (r : ℕ)
    (f : α → Multiset β) (hf : Function.Injective f)
    (hs : ∀a x, x ∈ f a → x ∈ s) (hr : ∀a, (f a).card ≤ r) :
    Nat.card α ≤ (s.card + 1).multichoose r := by
  let g : α → Sym (Option s) r := fun a => padMultiset s r (f a) (hs a) (hr a)
  have hg : Function.Injective g := by
    intro a b hab
    apply hf
    have H := congrArg (fun v : Sym (Option s) r =>
      v.val.filterMap (Option.map Subtype.val)) hab
    simpa only [g, decode_padMultiset] using H
  have H := Nat.card_le_card_of_injective g hg
  rw [Sym.natCard_sym_eq_multichoose] at H
  simpa only [Nat.card_eq_fintype_card, Fintype.card_option, Fintype.card_coe] using H

 

lemma idealCoefficient_prime_pow_le {p : ℕ} (hp : p.Prime) (r : ℕ) :
    idealCoefficient K (p^r) ≤ (r + Module.finrank ℤ (𝓞 K)).choose (Module.finrank ℤ (𝓞 K)) := by
  rw [idealCoefficient_pos K _ (pow_ne_zero _ hp.ne_zero)]
  let f : {I : Ideal (𝓞 K) // Ideal.absNorm I = p^r} → Multiset (Ideal (𝓞 K)) :=
    fun I => normalizedFactors I.1
  have hzero : ∀I : {I : Ideal (𝓞 K) // Ideal.absNorm I = p^r}, I.1 ≠ ⊥ := by
    intro I h
    have H : (0:ℕ) = p^r := by simpa [h] using I.2
    exact (pow_ne_zero _ hp.ne_zero) H.symm
  have hf : Function.Injective f := by
    intro I J h
    apply Subtype.ext
    have H := congrArg Multiset.prod h
    simpa only [f, Ideal.prod_normalizedFactors_eq_self (hzero I),
      Ideal.prod_normalizedFactors_eq_self (hzero J)] using H
  have H := card_le_of_multiset_encoding (idealsOverPrime K p) r f hf
    (fun I _ hP => ideal_factor_mem_over K hp I.2 hP)
    (fun I => ideal_factor_count_le K hp I.2)
  apply H.trans
  rw [Nat.multichoose_eq]
  calc
    _ ≤ (Module.finrank ℤ (𝓞 K) + r).choose r :=
      Nat.choose_le_choose r (by have := idealsOverPrime_card_le K hp; omega)
    _ = (r + Module.finrank ℤ (𝓞 K)).choose (Module.finrank ℤ (𝓞 K)) := by
      rw [Nat.add_comm (Module.finrank ℤ (𝓞 K)) r, Nat.choose_symm_add]

 
theorem idealCoefficient_le_divisor (m : ℕ) :
    idealCoefficient K m ≤ nFoldDivisor (Module.finrank ℤ (𝓞 K) + 1) m := by
  by_cases hm : m = 0
  · simp [hm,nFoldDivisor]
  unfold nFoldDivisor
  rw [(idealCoefficient_multiplicative K).multiplicative_factorization _ hm,
    ArithmeticFunction.isMultiplicative_zeta.pow.multiplicative_factorization _ hm]
  apply Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
  intro p hp
  have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
  exact (idealCoefficient_prime_pow_le K hprime _).trans_eq
    (nFoldDivisor_prime_pow _ _ _ hprime).symm

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
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
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


namespace PrimeDegreePackets
variable (K : Type*) [Field K] [NumberField K]


lemma coprimeIdealCoefficient_bounds (q m : ℕ) :
    0 ≤ coprimeIdealCoefficient K q m ∧
      coprimeIdealCoefficient K q m ≤
        (nFoldDivisor (Module.finrank ℤ (𝓞 K)+1) m : ℝ) := by
  simp only [coprimeIdealCoefficient,ArithmeticFunction.coe_mk]
  split_ifs
  · exact ⟨idealCoefficientReal_nonneg K m, by
      change (idealCoefficient K m : ℝ) ≤ _
      exact_mod_cast idealCoefficient_le_divisor K m⟩
  · exact ⟨le_rfl, Nat.cast_nonneg _⟩

end PrimeDegreePackets


end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_LocalEuler
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.globalLabelsMulAction _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.FullLattice.toPacket_carrier _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.OAI.PrimeDegreePackets.globalLabels_smul_val _root_.infinitePlace_mult_smul
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



lemma coprimeIntegralIdeal_norm_tsum {K : Type*} [Field K] [NumberField K]
    (q : ℕ) (hq : q ≠ 0) (F : ℕ → ℝ≥0∞) :
    (∑' I : coprimeIntegralIdeals K q.primeFactors, F (Ideal.absNorm I.1.1)) =
      ∑' m : ℕ, ENNReal.ofReal (coprimeIdealCoefficient K q m) * F m := by
  classical
  have he : (∑' I : coprimeIntegralIdeals K q.primeFactors, F (Ideal.absNorm I.1.1)) =
      ∑' I : {I : {J : Ideal (𝓞 K) // J ≠ ⊥} // (Ideal.absNorm I.1).Coprime q},
        F (Ideal.absNorm I.1.1) := (coprimeIdealSubtypeEquiv (K := K) q hq).tsum_eq
          (fun I => F (Ideal.absNorm I.1.1))
  rw [he]
  have hsub := tsum_subtype
    {I : {J : Ideal (𝓞 K) // J ≠ ⊥} | (Ideal.absNorm I.1).Coprime q}
    (fun I => F (Ideal.absNorm I.1))
  simp only [Set.indicator, Set.mem_ofPred_eq] at hsub
  have hsub' : (∑' I : {I : {J : Ideal (𝓞 K) // J ≠ ⊥} // (Ideal.absNorm I.1).Coprime q},
      F (Ideal.absNorm I.1.1)) =
    (∑' I : {J : Ideal (𝓞 K) // J ≠ ⊥},
      if (Ideal.absNorm I.1).Coprime q then F (Ideal.absNorm I.1) else 0) := hsub
  rw [hsub']
  rw [integralIdeal_norm_tsum (fun m => if m.Coprime q then F m else 0)]
  apply tsum_congr
  intro m
  change (idealCoefficient K m : ℝ≥0∞) * (if m.Coprime q then F m else 0) =
    ENNReal.ofReal (if m.Coprime q then (idealCoefficient K m : ℝ) else 0) * F m
  split_ifs <;> simp only [mul_zero, zero_mul, ENNReal.ofReal_zero, ENNReal.ofReal_natCast]

end PrimeDegreePackets


namespace PrimeDegreePackets
open NumberField Finset
open scoped BigOperators ENNReal nonZeroDivisors

 
lemma coprimeIdeal_interval_tsum {K : Type*} [Field K] [NumberField K]
    (q : ℕ) (hq : q ≠ 0) (a b d : ℕ) (hd : 0 < d) :
    (∑' J : coprimeIntegralIdeals K q.primeFactors,
      if a < d * Ideal.absNorm J.1.1 ∧ d * Ideal.absNorm J.1.1 ≤ b then (1 : ℝ≥0∞) else 0) =
      ENNReal.ofReal (∑ m ∈ Ioc (a / d) (b / d), coprimeIdealCoefficient K q m) := by
  classical
  rw [coprimeIntegralIdeal_norm_tsum q hq
    (fun m => if a < d*m ∧ d*m ≤ b then (1:ℝ≥0∞) else 0)]
  have hc (m : ℕ) : (a < d*m ∧ d*m ≤ b) ↔ m ∈ Finset.Ioc (a/d) (b/d) := by
    simp only [Finset.mem_Ioc, Nat.div_lt_iff_lt_mul hd, Nat.le_div_iff_mul_le hd, Nat.mul_comm]
  simp_rw [hc, mul_ite, mul_one, mul_zero]
  rw [tsum_eq_sum (s := Finset.Ioc (a/d) (b/d)) (fun m hm => by simp [hm])]
  simp only [Finset.sum_ite_mem, Finset.inter_self]
  rw [ENNReal.ofReal_sum_of_nonneg (fun m _ => (coprimeIdealCoefficient_bounds K q m).1)]



theorem weightedIdealInterval_convolution {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (a b : ℕ) :
    weightedIdealInterval M a b =
      ∑' I : primaryIntegralIdeals K (saturationIndex M).primeFactors,
        globalIdealWeight M (nonzeroIntegralIdealUnit I.1) *
          ENNReal.ofReal (∑ m ∈ Ioc (a / Ideal.absNorm I.1.1) (b / Ideal.absNorm I.1.1),
            coprimeIdealCoefficient K (saturationIndex M) m) := by
  classical
  have h := weighted_ideal_convolution M
    (fun m => if a < m ∧ m ≤ b then (1:ℝ≥0∞) else 0)
  simp only [mul_ite,mul_one,mul_zero] at h
  rw [weightedIdealInterval, h]
  apply tsum_congr
  intro I
  rw [coprimeIdeal_interval_tsum (saturationIndex M) (saturationIndex_ne_zero M) a b _
    (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr I.1.2))]


end PrimeDegreePackets


namespace PrimeDegreePackets
open NumberField Finset
open scoped BigOperators ENNReal nonZeroDivisors

lemma coprimeIdeal_interval_elementary {K : Type*} [Field K] [NumberField K]
    {n : ℕ} (hn : Module.finrank ℤ (𝓞 K) = n) (q a b d : ℕ) (hb : 0 < b) (hd : 0 < d) :
    (∑ m ∈ Ioc (a / d) (b / d), coprimeIdealCoefficient K q m) ≤
      ((b:ℝ)/d) * (1 + Real.log b)^n := by
  have hnonneg : 0 ≤ 1 + Real.log (b : ℝ) := by
    have := Real.log_nonneg (by exact_mod_cast hb : (1:ℝ) ≤ b)
    linarith
  by_cases hz : b/d = 0
  · simp only [hz,Finset.Ioc_eq_empty_of_le (Nat.zero_le _), sum_empty]
    positivity
  have hpos : 0 < b/d := Nat.pos_of_ne_zero hz
  have hlog : Real.log ((b/d : ℕ):ℝ) ≤ Real.log (b:ℝ) :=
    Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast Nat.div_le_self b d)
  have hbase : 0 ≤ 1 + Real.log ((b/d : ℕ):ℝ) := by
    have := Real.log_nonneg (by exact_mod_cast hpos : (1:ℝ) ≤ (b/d : ℕ))
    linarith
  calc
    _ ≤ ∑ m ∈ Icc 1 (b/d), coprimeIdealCoefficient K q m := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro m hm
        exact Finset.mem_Icc.mpr ⟨Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp hm).1), (Finset.mem_Ioc.mp hm).2⟩
      · intro m _ _
        exact (coprimeIdealCoefficient_bounds K q m).1
    _ ≤ ∑ m ∈ Icc 1 (b/d), (nFoldDivisor (n+1) m : ℝ) := by
      apply sum_le_sum
      intro m _
      simpa only [hn] using (coprimeIdealCoefficient_bounds K q m).2
    _ ≤ (b/d : ℕ) * (1+Real.log ((b/d : ℕ):ℝ))^n := nFoldDivisor_summatory_le n (b/d)
    _ ≤ _ := mul_le_mul Nat.cast_div_le (pow_le_pow_left₀ hbase (by linarith) n)
      (pow_nonneg hbase n) (by positivity)

 

theorem weightedIdeal_large_norm_bound {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n) (hn0 : 0 < n)
    (a b : ℕ) (hb : 0 < b) (Q : ℝ) (hQ : 0 < Q)
    (hqQ : (saturationIndex M : ℝ) ≤ Q) :
    let s : ℝ := 1 / (2 * (n : ℝ))
    let hε : 0 < s / 16 := by dsimp [s] <;> positivity
    (∑' I : primaryIntegralIdeals K (saturationIndex M).primeFactors,
      if ENNReal.ofReal Q ^ (1/8 : ℝ) < (Ideal.absNorm I.1.1 : ℝ≥0∞)
      then globalIdealWeight M (nonzeroIntegralIdealUnit I.1) *
        ENNReal.ofReal (∑ m ∈ Ioc (a / Ideal.absNorm I.1.1) (b / Ideal.absNorm I.1.1),
          coprimeIdealCoefficient K (saturationIndex M) m)
      else 0) ≤
        ENNReal.ofReal ((b:ℝ) * (1+Real.log b)^n) *
          ((saturationIndex M : ℝ≥0∞)⁻¹ *
            ENNReal.ofReal (localProductConstant n (s / 16) hε) *
            ENNReal.ofReal Q ^ (-s / 16)) := by
  dsimp only
  have hnZ : Module.finrank ℤ (𝓞 K) = n := by
    rw [NumberField.RingOfIntegers.rank]; exact hn
  have hB : 0 ≤ (b:ℝ) * (1+Real.log b)^n := by
    apply mul_nonneg (Nat.cast_nonneg _)
    apply pow_nonneg
    have := Real.log_nonneg (by exact_mod_cast hb : (1:ℝ) ≤ b)
    linarith
  calc
    _ ≤ ENNReal.ofReal ((b:ℝ)*(1+Real.log b)^n) *
        ∑' I : primaryIntegralIdeals K (saturationIndex M).primeFactors,
          if ENNReal.ofReal Q ^ (1/8 : ℝ) < (Ideal.absNorm I.1.1 : ℝ≥0∞)
          then globalIdealWeight M (nonzeroIntegralIdealUnit I.1) / (Ideal.absNorm I.1.1 : ℝ≥0∞)
          else 0 := by
      rw [← ENNReal.tsum_mul_left]
      apply ENNReal.tsum_le_tsum
      intro I
      split_ifs with h
      · have hd : 0 < Ideal.absNorm I.1.1 :=
          Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr I.1.2)
        have H := ENNReal.ofReal_le_ofReal
          (coprimeIdeal_interval_elementary hnZ (saturationIndex M) a b _ hb hd)
        refine (mul_le_mul_right H _).trans_eq ?_
        rw [show ((b:ℝ)/Ideal.absNorm I.1.1)*(1+Real.log b)^n =
          ((b:ℝ)*(1+Real.log b)^n) / Ideal.absNorm I.1.1 by ring,
          ENNReal.ofReal_div_of_pos (Nat.cast_pos.mpr hd), ENNReal.ofReal_natCast]
        simp only [div_eq_mul_inv]
        ac_rfl
      · simp
    _ ≤ _ := mul_le_mul_right (primaryIdeal_reciprocal_tail M hn hn0 Q hQ hqQ) _

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
-- module Solutions.OAIQ244_DUKE.PrimePackets_IntervalGeometry
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.globalLabelsMulAction _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.FullLattice.toPacket_carrier _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.OAI.PrimeDegreePackets.globalLabels_smul_val _root_.infinitePlace_mult_smul
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

lemma weightedIdealInterval_split {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (a b T : ℕ) :
    weightedIdealInterval M a b =
      (∑' I : primaryIntegralIdeals K (saturationIndex M).primeFactors,
        if Ideal.absNorm I.1.1 ≤ T then globalIdealWeight M (nonzeroIntegralIdealUnit I.1) *
          ENNReal.ofReal (∑ m ∈ Ioc (a / Ideal.absNorm I.1.1) (b / Ideal.absNorm I.1.1),
            coprimeIdealCoefficient K (saturationIndex M) m) else 0) +
      ∑' I : primaryIntegralIdeals K (saturationIndex M).primeFactors,
        if T < Ideal.absNorm I.1.1 then globalIdealWeight M (nonzeroIntegralIdealUnit I.1) *
          ENNReal.ofReal (∑ m ∈ Ioc (a / Ideal.absNorm I.1.1) (b / Ideal.absNorm I.1.1),
            coprimeIdealCoefficient K (saturationIndex M) m) else 0 := by
  classical
  rw [weightedIdealInterval_convolution, ← ENNReal.tsum_add]
  apply tsum_congr
  intro I
  by_cases h : Ideal.absNorm I.1.1 ≤ T
  · simp only [h,not_lt.mpr h,ite_true, if_true,ite_false, if_false,add_zero]
  · simp only [h,lt_of_not_ge h,ite_true, if_true,ite_false, if_false,zero_add]



end PrimeDegreePackets


namespace PrimeDegreePackets

lemma weighted_cutoff_div_lower {Q : ℝ} (hQ : 1 ≤ Q) {b : ℕ}
    (hb : Q^(3/4:ℝ) ≤ (b:ℝ)) :
    Q^(5/8:ℝ)-1 < (b / ⌊Q^(1/8:ℝ)⌋₊ : ℕ) := by
  let T : ℕ := ⌊Q^(1/8:ℝ)⌋₊
  have hQ0 : 0 < Q := lt_of_lt_of_le zero_lt_one hQ
  have hT : 0 < T := Nat.floor_pos.mpr (Real.one_le_rpow hQ (by norm_num))
  have hTle : (T:ℝ) ≤ Q^(1/8:ℝ) := Nat.floor_le (Real.rpow_nonneg hQ0.le _)
  have hT0 : (0:ℝ) < T := Nat.cast_pos.mpr hT
  have hratio : Q^(5/8:ℝ) ≤ (b:ℝ)/T := by
    apply (le_div_iff₀ hT0).mpr
    calc
      _ ≤ Q^(5/8:ℝ) * Q^(1/8:ℝ) := mul_le_mul_of_nonneg_left hTle (by positivity)
      _ = Q^(3/4:ℝ) := by rw [← Real.rpow_add hQ0]; norm_num
      _ ≤ _ := hb
  have hmod : ((b%T:ℕ):ℝ) < T := by exact_mod_cast Nat.mod_lt b hT
  have heq : (T:ℝ)*(b/T:ℕ)+(b%T:ℕ)=b := by exact_mod_cast Nat.div_add_mod b T
  have hbdiv : (b:ℝ)/T < (b/T:ℕ)+1 := by
    apply (div_lt_iff₀ hT0).mpr
    nlinarith
  exact (sub_lt_iff_lt_add.mpr (hratio.trans_lt hbdiv))

 

lemma eventual_weighted_small_parameters (R : ℕ) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ Q : ℝ in atTop, 1 ≤ Q ∧ ∀ q b : ℕ, 0 < q → (q:ℝ) ≤ Q →
      Q^(3/4:ℝ) ≤ (b:ℝ) →
      0 < ⌊Q^(1/8:ℝ)⌋₊ ∧ R ≤ b/⌊Q^(1/8:ℝ)⌋₊ ∧
      Real.log q ≤ (b/⌊Q^(1/8:ℝ)⌋₊:ℕ) ∧
      4*⌊Q^(1/8:ℝ)⌋₊^2 ≤ b ∧ 2 ≤ η*(b/⌊Q^(1/8:ℝ)⌋₊:ℕ) := by
  have hlog := (isLittleO_log_rpow_atTop (by norm_num : (0:ℝ)<5/8)).bound
    (by norm_num : (0:ℝ)<1/2)
  filter_upwards [eventually_ge_atTop (1:ℝ),hlog,
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<5/8)).eventually_ge_atTop
      (max ((R:ℝ)+1) (max 2 (2/η+1))),
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/2)).eventually_ge_atTop 4]
    with Q hQ hlog hbig hhalf
  refine ⟨hQ,?_⟩
  intro q b hq hqQ hb
  let T : ℕ := ⌊Q^(1/8:ℝ)⌋₊
  have hQ0 : 0 < Q := lt_of_lt_of_le zero_lt_one hQ
  have hT : 0 < T := Nat.floor_pos.mpr (Real.one_le_rpow hQ (by norm_num))
  have hTle : (T:ℝ) ≤ Q^(1/8:ℝ) := Nat.floor_le (Real.rpow_nonneg hQ0.le _)
  have hdiv := weighted_cutoff_div_lower hQ hb
  have hbig1 : (R:ℝ)+1 ≤ Q^(5/8:ℝ) := (le_max_left _ _).trans hbig
  have hbig2 : 2 ≤ Q^(5/8:ℝ) := (le_max_left _ _).trans ((le_max_right _ _).trans hbig)
  have hbig3 : 2/η+1 ≤ Q^(5/8:ℝ) := (le_max_right _ _).trans ((le_max_right _ _).trans hbig)
  have hRT : R ≤ b/T := by exact_mod_cast (show (R:ℝ) ≤ (b/T:ℕ) by linarith)
  have hqlog : Real.log q ≤ (b/T:ℕ) := by
    have hqq : Real.log q ≤ Real.log Q := Real.log_le_log (Nat.cast_pos.mpr hq) hqQ
    simp only [Real.norm_eq_abs,abs_of_nonneg (Real.log_nonneg hQ),
      abs_of_nonneg (Real.rpow_nonneg hQ0.le _)] at hlog
    linarith
  have hsq : 4*T^2 ≤ b := by
    have H : (4:ℝ)*(T:ℝ)^2 ≤ b := by
      calc
        _ ≤ 4*(Q^(1/8:ℝ))^2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hTle 2) (by norm_num)
        _ = Q^(1/4:ℝ)*4 := by rw [← Real.rpow_mul_natCast hQ0.le]; norm_num <;> ring
        _ ≤ Q^(1/4:ℝ)*Q^(1/2:ℝ) := mul_le_mul_of_nonneg_left hhalf (by positivity)
        _ = Q^(3/4:ℝ) := by rw [← Real.rpow_add hQ0]; norm_num
        _ ≤ _ := hb
    exact_mod_cast H
  refine ⟨hT,hRT,hqlog,hsq,?_⟩
  have H : 2/η ≤ (b/T:ℕ) := by linarith
  have := (div_le_iff₀ hη).mp H
  simpa only [mul_comm] using this

lemma weighted_cutoff_large_iff {Q : ℝ} (hQ : 0 ≤ Q) (d : ℕ) :
    ⌊Q^(1/8:ℝ)⌋₊ < d ↔ ENNReal.ofReal Q ^ (1/8:ℝ) < (d:ℝ≥0∞) := by
  rw [Nat.floor_lt (Real.rpow_nonneg hQ _), ENNReal.ofReal_rpow_of_nonneg hQ (by norm_num)]
  by_cases hd : d = 0
  · simp [hd,Real.rpow_nonneg hQ _]
  · rw [← ENNReal.ofReal_natCast, ENNReal.ofReal_lt_ofReal_iff (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hd))]

end PrimeDegreePackets


namespace PrimeDegreePackets

lemma weighted_log_power_error (n : ℕ) (ε C : ℝ) (hε : 0 < ε) :
    Tendsto (fun Q : ℝ => C * (2*3^n) * (Real.log Q)^(n+1) / Q^ε) atTop (𝓝 0) := by
  have H := (isLittleO_log_rpow_rpow_atTop ((n+1:ℕ):ℝ) hε).tendsto_div_nhds_zero
  simp only [Real.rpow_natCast] at H
  simpa only [mul_div_assoc,mul_zero] using
    (tendsto_const_nhds.mul H : Tendsto (fun Q : ℝ =>
      (C*(2*3^n))*((Real.log Q)^(n+1)/Q^ε)) atTop (𝓝 ((C*(2*3^n))*0)))

 

lemma eventual_weighted_tail_absorption (n : ℕ) (ε C η A₀ : ℝ)
    (hε : 0 < ε) (hC : 0 ≤ C) (hη : 0 < η) (hA : 1 ≤ A₀) :
    ∀ᶠ Q : ℝ in atTop, 0 < Q ∧ ∀ a b : ℕ, 2 ≤ b →
      (b:ℝ) ≤ A₀*Q → η*b ≤ (b:ℝ)-a →
      C * ((b:ℝ)*(1+Real.log b)^n) * Q^(-ε) ≤ ((b:ℝ)-a)/Real.log b := by
  filter_upwards [eventually_ge_atTop (max 1 A₀),
    Real.tendsto_log_atTop.eventually_ge_atTop 1,
    (weighted_log_power_error n ε C hε).eventually_le_const hη]
    with Q hQ hlogQ herr
  have hQ1 : 1 ≤ Q := (le_max_left _ _).trans hQ
  have hQ0 : 0 < Q := lt_of_lt_of_le zero_lt_one hQ1
  have hAQ : A₀ ≤ Q := (le_max_right _ _).trans hQ
  have hA0 : 0 < A₀ := lt_of_lt_of_le zero_lt_one hA
  refine ⟨hQ0,?_⟩
  intro a b hb hbQ hrel
  have hb0 : (0:ℝ) < b := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hb)
  have hlogb : 0 < Real.log (b:ℝ) := Real.log_pos (by exact_mod_cast hb : (1:ℝ)<b)
  have hlog : Real.log (b:ℝ) ≤ 2*Real.log Q := by
    have Hb := Real.log_le_log hb0 hbQ
    rw [Real.log_mul hA0.ne' hQ0.ne'] at Hb
    have HA := Real.log_le_log hA0 hAQ
    linarith
  have hbase : 0 ≤ 1+Real.log (b:ℝ) := by linarith
  have hbaseQ : 1+Real.log (b:ℝ) ≤ 3*Real.log Q := by linarith
  have hkernel : (Real.log (b:ℝ)*(1+Real.log b)^n)*Q^(-ε) ≤
      (2*3^n)*(Real.log Q)^(n+1)/Q^ε := by
    calc
      _ ≤ ((2*Real.log Q)*(3*Real.log Q)^n)*Q^(-ε) := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hQ0.le _)
        exact mul_le_mul hlog (pow_le_pow_left₀ hbase hbaseQ n)
          (pow_nonneg hbase n) (by linarith)
      _ = _ := by rw [Real.rpow_neg hQ0.le,mul_pow,pow_succ]; ring
  have hkernelC : C*((Real.log (b:ℝ)*(1+Real.log b)^n)*Q^(-ε)) ≤ η := by
    calc
      _ ≤ C*((2*3^n)*(Real.log Q)^(n+1)/Q^ε) := mul_le_mul_of_nonneg_left hkernel hC
      _ = C*(2*3^n)*(Real.log Q)^(n+1)/Q^ε := by ring
      _ ≤ _ := herr
  apply (le_div_iff₀ hlogb).mpr
  have H := mul_le_mul_of_nonneg_left hkernelC hb0.le
  calc
    _ = (b:ℝ)*(C*((Real.log (b:ℝ)*(1+Real.log b)^n)*Q^(-ε))) := by ring
    _ ≤ (b:ℝ)*η := H
    _ ≤ _ := by simpa only [mul_comm] using hrel

end PrimeDegreePackets


namespace PrimeDegreePackets
open NumberField Finset Filter Topology
open scoped BigOperators ENNReal nonZeroDivisors

lemma dedekindZeta_real_one_le (K : Type*) [Field K] [NumberField K]
    {s : ℝ} (hs : 1 < s) : 1 ≤ (NumberField.dedekindZeta K s).re := by
  rw [dedekindZeta_real_eq_terms]
  have H := (idealCoefficient_real_summable K hs).le_tsum 1
    (fun m _ => realDirichletTerm_nonneg (idealCoefficientReal_nonneg K) s m)
  simpa [realDirichletTerm,idealCoefficientReal,idealCoefficient_one] using H

 

theorem weightedIdeal_interval_zeta_bound (n : ℕ) (hn0 : 0 < n) :
    ∃ C : ℝ, 0 < C ∧ ∀ A₀ : ℝ, 1 ≤ A₀ → ∀ η : ℝ, 0 < η →
      ∀ᶠ Q : ℝ in atTop,
      ∀ (K : Type*) [Field K] [NumberField K] (M : FullLattice n K),
        Module.finrank ℚ K = n → (saturationIndex M : ℝ) ≤ Q →
        ∀ a b : ℕ, Q^(3/4:ℝ) ≤ (b:ℝ) → (b:ℝ) ≤ A₀*Q →
          a ≤ b → η*b ≤ (b:ℝ)-a →
          weightedIdealInterval M a b ≤ (saturationIndex M : ℝ≥0∞)⁻¹ *
            ENNReal.ofReal (C * ((b:ℝ)-a) *
              ((NumberField.dedekindZeta K (1+1/Real.log b)).re / Real.log b)) := by
  classical
  obtain ⟨C,hC,Hsmall⟩ := weightedIdeal_small_norm_bound n
  refine ⟨C+1,by linarith,?_⟩
  intro A₀ hA η hη
  obtain ⟨R,hR⟩ := Hsmall η hη
  let s : ℝ := 1/(2*(n:ℝ))
  have hs : 0 < s := by dsimp [s] <;> positivity
  have hε : 0 < s/16 := by positivity
  let Ctail : ℝ := localProductConstant n (s/16) hε
  have hCtail : 0 < Ctail := localProductConstant_pos n _ hε
  filter_upwards [eventual_weighted_small_parameters R η hη,
    eventual_weighted_tail_absorption n (s/16) Ctail η A₀ hε hCtail.le hη hA,
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<3/4)).eventually_ge_atTop 2]
    with Q hparam htail hQb
  intro K _ _ M hn hqQ a b hQb' hbQ hab hrel
  have hQ0 : 0 < Q := htail.1
  have hb : 2 ≤ b := by exact_mod_cast hQb.trans hQb'
  have hb0 : 0 < b := lt_of_lt_of_le (by decide : 0 < 2) hb
  have hlogb : 0 < Real.log (b:ℝ) := Real.log_pos (by exact_mod_cast hb : (1:ℝ)<b)
  have hΔ : 0 ≤ (b:ℝ)-a := sub_nonneg.mpr (by exact_mod_cast hab)
  have hz : 1 ≤ (NumberField.dedekindZeta K (1+1/Real.log b)).re := by
    have H := dedekindZeta_real_one_le K
      (show 1 < 1+1/Real.log (b:ℝ) by linarith [one_div_pos.mpr hlogb])
    simpa only [Complex.ofReal_add,Complex.ofReal_div,Complex.ofReal_one] using H
  let Z : ℝ := (NumberField.dedekindZeta K (1+1/Real.log b)).re / Real.log b
  have hZ : 0 ≤ Z := div_nonneg (by linarith) hlogb.le
  let T : ℕ := ⌊Q^(1/8:ℝ)⌋₊
  obtain ⟨hT,hRT,hqlog,hsquare,hlong⟩ := hparam.2 (saturationIndex M) b
    (Nat.pos_of_ne_zero (saturationIndex_ne_zero M)) hqQ hQb'
  have HS := hR K M hn a b T hT hRT hqlog hsquare hab hrel hlong
  have HL := weightedIdeal_large_norm_bound M hn hn0 a b hb0 Q hQ0 hqQ
  change (∑' I : primaryIntegralIdeals K (saturationIndex M).primeFactors,
      if ENNReal.ofReal Q^(1/8:ℝ) < (Ideal.absNorm I.1.1:ℝ≥0∞)
      then globalIdealWeight M (nonzeroIntegralIdealUnit I.1) *
        ENNReal.ofReal (∑ m ∈ Ioc (a/Ideal.absNorm I.1.1) (b/Ideal.absNorm I.1.1),
          coprimeIdealCoefficient K (saturationIndex M) m) else 0) ≤
      ENNReal.ofReal ((b:ℝ)*(1+Real.log b)^n) *
        ((saturationIndex M:ℝ≥0∞)⁻¹*ENNReal.ofReal Ctail*ENNReal.ofReal Q^(-s/16)) at HL
  have hbase : 0 ≤ (b:ℝ)*(1+Real.log b)^n :=
    mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (by linarith) n)
  have htailZ : Ctail*((b:ℝ)*(1+Real.log b)^n)*Q^(-s/16) ≤ ((b:ℝ)-a)*Z := by
    calc
      _ ≤ ((b:ℝ)-a)/Real.log b := by
        simpa only [neg_div] using htail.2 a b hb hbQ hrel
      _ ≤ _ := by
        dsimp [Z]
        have := mul_le_mul_of_nonneg_left hz hΔ
        exact (div_le_div_of_nonneg_right (by simpa only [mul_one] using this) hlogb.le).trans_eq (by ring)
  have HL' : (∑' I : primaryIntegralIdeals K (saturationIndex M).primeFactors,
      if T < Ideal.absNorm I.1.1 then globalIdealWeight M (nonzeroIntegralIdealUnit I.1) *
        ENNReal.ofReal (∑ m ∈ Ioc (a/Ideal.absNorm I.1.1) (b/Ideal.absNorm I.1.1),
          coprimeIdealCoefficient K (saturationIndex M) m) else 0) ≤
        (saturationIndex M:ℝ≥0∞)⁻¹ * ENNReal.ofReal (((b:ℝ)-a)*Z) := by
    simp_rw [show T = ⌊Q^(1/8:ℝ)⌋₊ from rfl,weighted_cutoff_large_iff hQ0.le]
    apply HL.trans
    calc
      _ = (saturationIndex M:ℝ≥0∞)⁻¹ *
          ENNReal.ofReal (Ctail*((b:ℝ)*(1+Real.log b)^n)*Q^(-s/16)) := by
        rw [ENNReal.ofReal_mul (mul_nonneg hCtail.le hbase),ENNReal.ofReal_mul hCtail.le,
          ENNReal.ofReal_rpow_of_pos hQ0]
        ac_rfl
      _ ≤ _ := mul_le_mul_right (ENNReal.ofReal_le_ofReal htailZ) _
  calc
    weightedIdealInterval M a b ≤
        (saturationIndex M:ℝ≥0∞)⁻¹ * ENNReal.ofReal (C*((b:ℝ)-a)*Z) +
        (saturationIndex M:ℝ≥0∞)⁻¹ * ENNReal.ofReal (((b:ℝ)-a)*Z) := by
      rw [weightedIdealInterval_split M a b T]
      exact add_le_add HS HL'
    _ = _ := by
      rw [← mul_add, ← ENNReal.ofReal_add (mul_nonneg (mul_nonneg hC.le hΔ) hZ)
        (mul_nonneg hΔ hZ)]
      congr 2
      change C*((b:ℝ)-a)*Z+((b:ℝ)-a)*Z = (C+1)*((b:ℝ)-a)*Z
      ring

end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_ZetaResidues
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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

lemma rounded_relative_interval {x y η : ℝ} (_hx : 1 ≤ x) (hy : 2 ≤ y)
    (hη : 0 < η) (hrel : η*x ≤ y) (hyx : y ≤ x) :
    ⌊x-y⌋₊ ≤ ⌈x⌉₊ ∧ x ≤ (⌈x⌉₊:ℝ) ∧ (⌈x⌉₊:ℝ) ≤ x+1 ∧
    η/2*(⌈x⌉₊:ℝ) ≤ (⌈x⌉₊:ℝ)-(⌊x-y⌋₊:ℝ) ∧
    (⌈x⌉₊:ℝ)-(⌊x-y⌋₊:ℝ) ≤ 2*y := by
  have hceil := Nat.le_ceil x
  have hceil' := (Nat.ceil_lt_add_one (by linarith : 0 ≤ x)).le
  have hfloor := Nat.floor_le (show 0 ≤ x-y by linarith)
  have hfloor' := Nat.lt_floor_add_one (x-y)
  have hab : ⌊x-y⌋₊ ≤ ⌈x⌉₊ := by exact_mod_cast (by linarith : (⌊x-y⌋₊:ℝ) ≤ (⌈x⌉₊:ℝ))
  refine ⟨hab,hceil,hceil',?_,by linarith⟩
  have H : η/2*(⌈x⌉₊:ℝ) ≤ η*x := by nlinarith
  exact H.trans (by linarith)

lemma eventual_rounding_parameters (A₀ η : ℝ) (_hA : 1 ≤ A₀) (hη : 0 < η) :
    ∀ᶠ Q : ℝ in atTop, ∀ x y : ℝ, Q^(3/4:ℝ) ≤ x → x ≤ A₀*Q →
      η*x ≤ y → y ≤ x →
      1 ≤ Q ∧ ⌊x-y⌋₊ ≤ ⌈x⌉₊ ∧ Q^(3/4:ℝ) ≤ (⌈x⌉₊:ℝ) ∧
      (⌈x⌉₊:ℝ) ≤ (A₀+1)*Q ∧
      η/2*(⌈x⌉₊:ℝ) ≤ (⌈x⌉₊:ℝ)-(⌊x-y⌋₊:ℝ) ∧
      (⌈x⌉₊:ℝ)-(⌊x-y⌋₊:ℝ) ≤ 2*y := by
  have ht := tendsto_rpow_atTop (by norm_num : (0:ℝ)<3/4)
  filter_upwards [eventually_ge_atTop (1:ℝ),ht.eventually_ge_atTop 1,
    ht.eventually_ge_atTop (2/η)] with Q hQ hQ1 hQη
  intro x y hxl hxu hy hyx
  have hx : 1 ≤ x := hQ1.trans hxl
  have htwo : 2 ≤ y := by
    have : 2/η ≤ x := hQη.trans hxl
    have := (div_le_iff₀ hη).mp this
    nlinarith
  obtain ⟨hab,hceil,hceil',hrel,hw⟩ := rounded_relative_interval hx htwo hη hy hyx
  refine ⟨hQ,hab,hxl.trans hceil,?_,hrel,hw⟩
  nlinarith

end PrimeDegreePackets


namespace PrimeDegreePackets
open Filter Topology
open scoped ENNReal NumberField



lemma weightedIdealRealInterval_le_rounded {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (x y : ℝ) (hyx : y ≤ x) :
    weightedIdealRealInterval M x y ≤ weightedIdealInterval M ⌊x-y⌋₊ ⌈x⌉₊ := by
  classical
  apply ENNReal.tsum_le_tsum
  intro I
  split_ifs with h h' h'
  · rfl
  · exfalso
    apply h'
    refine ⟨(Nat.floor_lt (sub_nonneg.mpr hyx)).mpr h.1,?_⟩
    exact_mod_cast (h.2.trans (Nat.le_ceil x))
  · exact bot_le
  · rfl

 

theorem weightedIdeal_realInterval_zeta_bound (n : ℕ) (hn0 : 0 < n) :
    ∃ C : ℝ, 0 < C ∧ ∀ A₀ : ℝ, 1 ≤ A₀ → ∀ η : ℝ, 0 < η →
      ∀ᶠ Q : ℝ in atTop,
      ∀ (K : Type*) [Field K] [NumberField K] (M : FullLattice n K),
        Module.finrank ℚ K = n → (saturationIndex M : ℝ) ≤ Q →
        ∀ x y : ℝ, Q^(3/4:ℝ) ≤ x → x ≤ A₀*Q →
          η*x ≤ y → y ≤ x →
          weightedIdealRealInterval M x y ≤ (saturationIndex M : ℝ≥0∞)⁻¹ *
            ENNReal.ofReal (C*y*((NumberField.dedekindZeta K
              (1+1/Real.log (⌈x⌉₊:ℝ))).re / Real.log (⌈x⌉₊:ℝ))) := by
  obtain ⟨C,hC,H⟩ := weightedIdeal_interval_zeta_bound n hn0
  refine ⟨2*C,by positivity,?_⟩
  intro A₀ hA η hη
  filter_upwards [H (A₀+1) (by linarith) (η/2) (by positivity),
    eventual_rounding_parameters A₀ η hA hη,
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<3/4)).eventually_ge_atTop 2]
    with Q hQ hround hQ2
  intro K _ _ M hn hq x y hxl hxu hrel hyx
  obtain ⟨_,hab,hbl,hbu,hbrel,hwidth⟩ := hround x y hxl hxu hrel hyx
  have hb2 : (2:ℝ) ≤ (⌈x⌉₊:ℝ) := hQ2.trans hbl
  have hlog : 0 < Real.log (⌈x⌉₊:ℝ) := Real.log_pos (by linarith)
  have hz : 0 ≤ (NumberField.dedekindZeta K (1+1/Real.log (⌈x⌉₊:ℝ))).re := by
    have HZ := dedekindZeta_real_one_le K
      (show 1 < 1+1/Real.log (⌈x⌉₊:ℝ) by linarith [one_div_pos.mpr hlog])
    exact le_trans zero_le_one (by
      simpa only [Complex.ofReal_add,Complex.ofReal_div,Complex.ofReal_one] using HZ)
  apply (weightedIdealRealInterval_le_rounded M x y hyx).trans
  apply (hQ K M hn hq _ _ hbl hbu hab hbrel).trans
  apply mul_le_mul_right (ENNReal.ofReal_le_ofReal ?_) _
  calc
    C*((⌈x⌉₊:ℝ)-(⌊x-y⌋₊:ℝ))*_ ≤ C*(2*y)*_ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hwidth hC.le) (div_nonneg hz hlog.le)
    _ = _ := by ring



end PrimeDegreePackets

open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_HaarUniqueness
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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



theorem weightedIdeal_realInterval_of_zeta_scale_oai (n : ℕ) (hn0 : 0 < n)
    {A : ℝ} (hA : 0 < A)
    (Hscale : ∀ᶠ Q : ℝ in atTop,
      ∀ (K : Type u) [Field K] [NumberField K] [NumberField.IsTotallyReal K],
        (K →+* ℝ) → Module.finrank ℚ K = n →
        |(NumberField.discr K : ℝ)| ≤ Q^2 →
        ∀ b : ℝ, Q^(3/4:ℝ) ≤ b →
          realDedekindZeta K (1+1/Real.log b) / Real.log b ≤
            A*NumberField.dedekindZeta_residue K) :
    ∃ C : ℝ, 0 < C ∧ ∀ A₀ : ℝ, 1 ≤ A₀ → ∀ η : ℝ, 0 < η →
      ∀ᶠ Q : ℝ in atTop,
      ∀ (K : Type u) [Field K] [NumberField K] [NumberField.IsTotallyReal K]
        (M : FullLattice n K), (K →+* ℝ) →
        Module.finrank ℚ K = n → |(NumberField.discr K : ℝ)| ≤ Q^2 →
        (saturationIndex M : ℝ) ≤ Q →
        ∀ x y : ℝ, Q^(3/4:ℝ) ≤ x → x ≤ A₀*Q → η*x ≤ y → y ≤ x →
          weightedIdealRealInterval M x y ≤ (saturationIndex M : ℝ≥0∞)⁻¹ *
            ENNReal.ofReal (C*y*NumberField.dedekindZeta_residue K) := by
  obtain ⟨C,hC,H⟩ := weightedIdeal_realInterval_zeta_bound n hn0
  refine ⟨C*A,mul_pos hC hA,?_⟩
  intro A₀ hA₀ η hη
  filter_upwards [H A₀ hA₀ η hη,Hscale,eventually_ge_atTop (0:ℝ)] with Q hQ hscale hQ0
  intro K _ _ _ M σ hn hD hq x y hxl hxu hrel hyx
  have hceil : Q^(3/4:ℝ) ≤ (⌈x⌉₊:ℝ) := hxl.trans (Nat.le_ceil x)
  have HR := hscale K σ hn hD _ hceil
  have hy : 0 ≤ y := le_trans (mul_nonneg hη.le (le_trans (Real.rpow_nonneg hQ0 _) hxl)) hrel
  apply (hQ K M hn hq x y hxl hxu hrel hyx).trans
  apply mul_le_mul_right (ENNReal.ofReal_le_ofReal ?_) _
  calc
    C*y*((NumberField.dedekindZeta K (1+1/Real.log (⌈x⌉₊:ℝ))).re /
        Real.log (⌈x⌉₊:ℝ)) ≤ C*y*(A*NumberField.dedekindZeta_residue K) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC.le hy)
      simpa only [realDedekindZeta,Complex.ofReal_add,Complex.ofReal_one,
        Complex.ofReal_div] using HR
    _ = _ := by ring



open MeasureTheory ProbabilityTheory Matrix
open scoped Classical BigOperators


end PrimeDegreePackets
end
end

end OAI
end

theorem solution.{u} : type_of% @OAI.PrimeDegreePackets.weightedIdeal_realInterval_of_zeta_scale_oai.{u} := @OAI.PrimeDegreePackets.weightedIdeal_realInterval_of_zeta_scale_oai.{u}
