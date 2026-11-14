-- Prove2me | solution 1 for OAI.PrimeDegreePackets.global_local_weight_moment_of_support_prod_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T06:46:10.478005+00:00
-- url     : https://prove2.me/submissions/b277d9fa-a72c-490b-9a12-d61bc1565b38

import Mathlib
import Definitions.Def_OAIQ244Duke024

section
-- module Solutions.OAIQ244_DUKE.Compat
attribute [-instance] _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.xMeasurableSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.infiniteAdeleRingT2Space
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
-- module Solutions.OAIQ244_DUKE.PrimePackets_HaarBounds
attribute [-instance] _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.xMeasurableSpace _root_.OAI.PrimeDegreePackets.xT2Space _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedMaximalIdeal.instIsMaximal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.finiteIdeleGroupT2Space _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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
namespace PrimeDegreePackets

 

theorem haar_kernel_eq_inv_card {A B : Type*} [AddGroup A] [AddGroup B]
    [MeasurableSpace A] [MeasurableAdd A]
    (μ : Measure A) [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]
    (f : A →+ B) [Finite f.range] (hf : MeasurableSet (f.ker : Set A)) :
    μ (f.ker : Set A) = (Nat.card f.range : ℝ≥0∞)⁻¹ := by
  have hc : (Nat.card f.range : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  rw [← one_div (Nat.card f.range : ℝ≥0∞)]
  apply (ENNReal.eq_div_iff hc (by simp)).mpr
  simpa only [AddSubgroup.index_ker, measure_univ] using
    f.ker.index_mul_measure hf μ

 
theorem haar_kernel_le_inv_addOrderOf {A B : Type*} [AddGroup A] [AddGroup B]
    [MeasurableSpace A] [MeasurableAdd A]
    (μ : Measure A) [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]
    (f : A →+ B) [Finite f.range] (hf : MeasurableSet (f.ker : Set A)) (a : A) :
    μ (f.ker : Set A) ≤ (addOrderOf (f a) : ℝ≥0∞)⁻¹ := by
  rw [haar_kernel_eq_inv_card μ f hf, ENNReal.inv_le_inv]
  have h : addOrderOf (f a) ≤ Nat.card f.range := by
    have hx := @addOrderOf_le_card f.range _ (f.rangeRestrict a) _
    rwa [← addOrderOf_injective f.range.subtype Subtype.val_injective] at hx
  exact_mod_cast h



end PrimeDegreePackets

open IsDiscreteValuationRing IsLocalRing
namespace PrimeDegreePackets



lemma addVal_scalar_unit_mul_pow (p : ℕ) [Fact p.Prime]
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Algebra (PadicInt p) R] (e : ℕ)
    (he : addVal R (algebraMap (PadicInt p) R p) = e)
    (u : (PadicInt p)ˣ) (a : ℕ) :
    addVal R (algebraMap (PadicInt p) R ((u : PadicInt p) * (p : PadicInt p) ^ a)) =
      (a * e : ℕ) := by
  rw [map_mul, map_pow, addVal_mul, addVal_pow, he,
    addVal_eq_zero_iff.mpr (u.isUnit.map (algebraMap (PadicInt p) R)), zero_add]
  simp [nsmul_eq_mul]

 

theorem scalar_preimage_maximalIdeal_pow (p : ℕ) [Fact p.Prime]
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Algebra (PadicInt p) R] (e : ℕ) (he0 : 0 < e)
    (he : addVal R (algebraMap (PadicInt p) R p) = e) (k : ℕ) :
    Ideal.comap (algebraMap (PadicInt p) R) (IsLocalRing.maximalIdeal R ^ k) =
      Ideal.span {(p : PadicInt p) ^ (k ⌈/⌉ e)} := by
  ext x
  change algebraMap (PadicInt p) R x ∈ IsLocalRing.maximalIdeal R ^ k ↔ _
  by_cases hx : x = 0
  · simp [hx]
  obtain ⟨a, u, rfl⟩ := eq_unit_mul_pow_irreducible hx (PadicInt.irreducible_p (p := p))
  rw [mem_maximalIdeal_pow_iff_addVal, addVal_scalar_unit_mul_pow p e he,
    Ideal.mem_span_singleton, ← addVal_le_iff_dvd,
    (PadicInt.irreducible_p (p := p)).addVal_pow,
    addVal_def' u (PadicInt.irreducible_p (p := p)) a,
    ENat.natCast_le_natCast, ENat.natCast_le_natCast]
  simpa only [Nat.mul_comm] using (ceilDiv_le_iff_le_mul he0).symm

 

lemma natCast_mem_maximalIdeal_pow_iff (p : ℕ) [Fact p.Prime]
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Algebra (PadicInt p) R] (e : ℕ) (he0 : 0 < e)
    (he : addVal R (algebraMap (PadicInt p) R p) = e) (k m : ℕ) :
    (m : R) ∈ IsLocalRing.maximalIdeal R ^ k ↔ p ^ (k ⌈/⌉ e) ∣ m := by
  rw [← map_natCast (algebraMap (PadicInt p) R) m]
  change (m : PadicInt p) ∈ Ideal.comap (algebraMap (PadicInt p) R)
    (IsLocalRing.maximalIdeal R ^ k) ↔ _
  rw [scalar_preimage_maximalIdeal_pow p e he0 he k,
    ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_natCast]
  exact ZMod.natCast_eq_zero_iff _ _

 

theorem addOrderOf_quotient_unit (p : ℕ) [Fact p.Prime]
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Algebra (PadicInt p) R] (e : ℕ) (he0 : 0 < e)
    (he : addVal R (algebraMap (PadicInt p) R p) = e) (k : ℕ)
    (u : R) (hu : IsUnit u) :
    addOrderOf (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ k) u) =
      p ^ (k ⌈/⌉ e) := by
  let q := Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ k)
  have hq : IsUnit (q u) := hu.map q
  have hdiv : ∀ m : ℕ, addOrderOf (q u) ∣ m ↔ p ^ (k ⌈/⌉ e) ∣ m := by
    intro m
    rw [addOrderOf_dvd_iff_nsmul_eq_zero, nsmul_eq_mul, hq.mul_left_eq_zero]
    rw [← map_natCast q, Ideal.Quotient.eq_zero_iff_mem]
    exact natCast_mem_maximalIdeal_pow_iff p e he0 he k m
  exact Nat.dvd_antisymm ((hdiv _).mpr dvd_rfl) ((hdiv _).mp dvd_rfl)

 

lemma exists_unit_of_span_eq_top {R : Type*} [CommRing R]
    [IsLocalRing R] (S : Set R) (hS : Ideal.span S = ⊤) :
    ∃ x ∈ S, IsUnit x := by
  by_contra h
  push Not at h
  have hs : S ⊆ IsLocalRing.maximalIdeal R := by
    intro x hx
    exact h x hx
  have heq : IsLocalRing.maximalIdeal R = ⊤ := top_le_iff.mp (hS ▸ Ideal.span_le.mpr hs)
  exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top heq

end PrimeDegreePackets


namespace PrimeDegreePackets
open MeasureTheory Set IsDiscreteValuationRing IsLocalRing
open scoped ENNReal

 

theorem haar_dvr_projection_tail (p : ℕ) [Fact p.Prime]
    {R A : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Algebra (PadicInt p) R] [Finite (IsLocalRing.ResidueField R)]
    [AddGroup A] [MeasurableSpace A] [MeasurableAdd A]
    (μ : Measure A) [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]
    (φ : A →+ R) (hsat : Ideal.span (Set.range φ) = ⊤)
    (e : ℕ) (he0 : 0 < e)
    (he : addVal R (algebraMap (PadicInt p) R p) = e)
    (k : ℕ) (hM : MeasurableSet {x | φ x ∈ IsLocalRing.maximalIdeal R ^ k}) :
    μ {x | (k : ℕ∞) ≤ addVal R (φ x)} ≤ ((p : ℝ≥0∞) ^ (k ⌈/⌉ e))⁻¹ := by
  have : Finite (R ⧸ IsLocalRing.maximalIdeal R ^ k) :=
    IsLocalRing.finite_quotient_iff.mpr ⟨k, le_rfl⟩
  let f : A →+ R ⧸ IsLocalRing.maximalIdeal R ^ k :=
    (Ideal.Quotient.mk _).toAddMonoidHom.comp φ
  have hset : (f.ker : Set A) = {x | (k : ℕ∞) ≤ addVal R (φ x)} := by
    ext x
    change Ideal.Quotient.mk _ (φ x) = 0 ↔ _
    rw [Ideal.Quotient.eq_zero_iff_mem, mem_maximalIdeal_pow_iff_addVal]
    rfl
  have hf : MeasurableSet (f.ker : Set A) := by
    convert hM using 1
    all_goals try with_reducible_and_instances rfl
    ext x
    exact Ideal.Quotient.eq_zero_iff_mem
  obtain ⟨u, ⟨a, rfl⟩, hu⟩ := exists_unit_of_span_eq_top (Set.range φ) hsat
  have horder : addOrderOf (f a) = p ^ (k ⌈/⌉ e) :=
    addOrderOf_quotient_unit p e he0 he k (φ a) hu
  have ht := haar_kernel_le_inv_addOrderOf μ f hf a
  rwa [horder, Nat.cast_pow, hset] at ht

 

theorem haar_natVal_projection_tail (p : ℕ) [Fact p.Prime]
    {R A : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Algebra (PadicInt p) R] [Finite (IsLocalRing.ResidueField R)]
    [AddGroup A] [MeasurableSpace A] [MeasurableAdd A]
    (μ : Measure A) [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]
    (φ : A →+ R) (hsat : Ideal.span (Set.range φ) = ⊤)
    (e : ℕ) (he0 : 0 < e)
    (he : addVal R (algebraMap (PadicInt p) R p) = e)
    (k : ℕ) (hM : MeasurableSet {x | φ x ∈ IsLocalRing.maximalIdeal R ^ k}) :
    μ {x | k ≤ (addVal R (φ x)).toNat} ≤ ((p : ℝ≥0∞) ^ (k ⌈/⌉ e))⁻¹ := by
  apply (measure_mono ?_).trans (haar_dvr_projection_tail p μ φ hsat e he0 he k hM)
  intro x hx
  exact (ENat.natCast_le_natCast.mpr hx).trans (ENat.natCast_toNat_le_self _)

end PrimeDegreePackets


namespace PrimeDegreePackets
open MeasureTheory Set IsDiscreteValuationRing IsLocalRing
open scoped ENNReal

section CompactDVR
variable {R A : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [CompactSpace R] [T2Space R]
    [TopologicalSpace A] [MeasurableSpace A] [OpensMeasurableSpace A]

lemma measurableSet_dvr_tail {φ : A → R} (hφ : Continuous φ) (k : ℕ) :
    MeasurableSet {x | (k : ℕ∞) ≤ addVal R (φ x)} := by
  have heq : {x | (k : ℕ∞) ≤ addVal R (φ x)} = φ ⁻¹' ((IsLocalRing.maximalIdeal R ^ k : Ideal R) : Set R) := by
    ext x
    exact (mem_maximalIdeal_pow_iff_addVal _ _).symm
  rw [heq]
  exact ((isOpen_maximalIdeal_pow R k).preimage hφ).measurableSet

lemma measurable_dvr_val {φ : A → R} (hφ : Continuous φ) :
    Measurable (fun x => addVal R (φ x)) := by
  apply ENat.measurable_iff.mpr
  intro k
  have heq : (fun x => addVal R (φ x)) ⁻¹' {(k : ℕ∞)} =
      {x | (k : ℕ∞) ≤ addVal R (φ x)} \ {x | ((k + 1 : ℕ) : ℕ∞) ≤ addVal R (φ x)} := by
    ext x
    simp only [mem_preimage, mem_singleton_iff, Set.mem_sdiff, mem_ofPred_eq]
    induction addVal R (φ x) using ENat.recTopCoe with
    | top => simp
    | coe v => simp only [ENat.natCast_inj, ENat.natCast_le_natCast]; omega
  rw [heq]
  exact (measurableSet_dvr_tail hφ k).diff (measurableSet_dvr_tail hφ (k + 1))

lemma measurable_dvr_natVal {φ : A → R} (hφ : Continuous φ) :
    Measurable (fun x => (addVal R (φ x)).toNat) :=
  (Measurable.of_discrete : Measurable ENat.toNat).comp (measurable_dvr_val hφ)

end CompactDVR



end PrimeDegreePackets

open scoped ENNReal BigOperators
namespace PrimeDegreePackets

 
theorem lintegral_pow_le_of_nat_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (J : Ω → ℕ) (hJ : Measurable J)
    (r p c : ℝ≥0∞) (htail : ∀ a : ℕ, 1 ≤ a → μ {ω | a ≤ J ω} ≤ c / p ^ a) :
    (∫⁻ ω, r ^ J ω ∂μ) ≤ 1 + c * (r / p) * (1 - r / p)⁻¹ := by
  rw [← lintegral_map (Measurable.of_discrete : Measurable (fun a : ℕ => r ^ a)) hJ,
    lintegral_countable', tsum_eq_zero_add' ENNReal.summable]
  simp only [pow_zero, one_mul]
  apply add_le_add
  · exact prob_le_one
  · calc
      (∑' a : ℕ, r ^ (a + 1) * (Measure.map J μ) {a + 1}) ≤
          ∑' a : ℕ, c * (r / p) ^ (a + 1) := by
        apply ENNReal.tsum_le_tsum
        intro a
        rw [Measure.map_apply hJ (measurableSet_singleton _)]
        have hsubset : J ⁻¹' {a + 1} ⊆ {ω | a + 1 ≤ J ω} := by
          intro ω hω
          exact le_of_eq (Set.mem_singleton_iff.mp hω).symm
        calc
          r ^ (a + 1) * μ (J ⁻¹' {a + 1}) ≤ r ^ (a + 1) * (c / p ^ (a + 1)) :=
            mul_le_mul_right ((measure_mono hsubset).trans (htail (a + 1) (by omega))) _
          _ = c * (r / p) ^ (a + 1) := by simp only [div_eq_mul_inv, mul_pow, ENNReal.inv_pow]; ac_rfl
      _ = c * (r / p) * (1 - r / p)⁻¹ := by
        simp_rw [pow_succ, ← mul_assoc, mul_right_comm c]
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]

 
theorem sqrt_geometric_factor_le {p : ℝ} (hp : 2 ≤ p) :
    (Real.sqrt p / p) * (1 - Real.sqrt p / p)⁻¹ ≤ 4 / Real.sqrt p := by
  have hp0 : 0 < p := by linarith
  have hs0 : 0 < Real.sqrt p := Real.sqrt_pos_of_pos hp0
  have hsq : Real.sqrt p ^ 2 = p := Real.sq_sqrt hp0.le
  have hs1 : 1 < Real.sqrt p := by
    by_contra h
    have hh : Real.sqrt p ≤ 1 := le_of_not_gt h
    nlinarith [sq_nonneg (Real.sqrt p - 1)]
  have hs43 : (4 / 3 : ℝ) ≤ Real.sqrt p := by
    by_contra h
    have hh : Real.sqrt p < 4 / 3 := lt_of_not_ge h
    nlinarith [mul_nonneg hs0.le (by linarith : 0 ≤ 4 / 3 - Real.sqrt p)]
  have hsp : Real.sqrt p < p := by nlinarith
  have hden : 0 < 1 - Real.sqrt p / p := sub_pos.mpr ((div_lt_one hp0).mpr hsp)
  apply (le_div_iff₀ hs0).mpr
  rw [mul_assoc, inv_mul_eq_div, ← mul_div_assoc]
  apply (div_le_iff₀ hden).mpr
  field_simp
  nlinarith

 

theorem local_sqrt_moment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (J : Ω → ℕ) (hJ : Measurable J)
    (n : ℕ) (p : ℝ) (hp : 2 ≤ p)
    (htail : ∀ a : ℕ, 1 ≤ a → μ {ω | a ≤ J ω} ≤ (n : ℝ≥0∞) / (ENNReal.ofReal p) ^ a) :
    (∫⁻ ω, (ENNReal.ofReal (Real.sqrt p)) ^ J ω ∂μ) ≤
      1 + (n : ℝ≥0∞) * ENNReal.ofReal (4 / Real.sqrt p) := by
  have hp0 : 0 < p := by linarith
  have hs0 : 0 < Real.sqrt p := Real.sqrt_pos_of_pos hp0
  have hsq : Real.sqrt p ^ 2 = p := Real.sq_sqrt hp0.le
  have hs1 : 1 < Real.sqrt p := by
    by_contra h
    have hh : Real.sqrt p ≤ 1 := le_of_not_gt h
    nlinarith [sq_nonneg (Real.sqrt p - 1)]
  have hsp : Real.sqrt p < p := by nlinarith
  have hden : 0 < 1 - Real.sqrt p / p := sub_pos.mpr ((div_lt_one hp0).mpr hsp)
  have hratio : 0 ≤ Real.sqrt p / p := div_nonneg hs0.le hp0.le
  apply (lintegral_pow_le_of_nat_tail μ J hJ (ENNReal.ofReal (Real.sqrt p))
    (ENNReal.ofReal p) n htail).trans
  apply add_le_add_right
  rw [mul_assoc]
  apply mul_le_mul_right
  rw [← ENNReal.ofReal_div_of_pos hp0,
    ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 hratio,
    ← ENNReal.ofReal_inv_of_pos hden, ← ENNReal.ofReal_mul hratio]
  exact ENNReal.ofReal_le_ofReal (sqrt_geometric_factor_le hp)


lemma ramifiedMaximum_measurable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (e : ι → ℕ) (v : ι → Ω → ℕ) (hv : ∀ i, Measurable (v i)) :
    Measurable (fun ω => ramifiedMaximum e (fun i => v i ω)) := by
  exact (Measurable.of_discrete : Measurable (ramifiedMaximum e)).comp
    (Measurable.of_eval hv)

lemma ceilDiv_ramification_succ (e a : ℕ) (he : 0 < e) :
    (e * a + 1) ⌈/⌉ e = a + 1 := by
  rw [Nat.ceilDiv_eq_add_pred_div]
  have heq : e * a + 1 + e - 1 = (a + 1) * e := by
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm a e]
    omega
  rw [heq, Nat.mul_div_left _ he]

 
theorem ramifiedMaximum_tail {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) (e : ι → ℕ) (he : ∀ i, 0 < e i) (v : ι → Ω → ℕ)
    (p : ℝ≥0∞)
    (htail : ∀ i k, 1 ≤ k → μ {ω | k ≤ v i ω} ≤ p⁻¹ ^ (k ⌈/⌉ e i))
    (a : ℕ) (ha : 1 ≤ a) :
    μ {ω | a ≤ ramifiedMaximum e (fun i => v i ω)} ≤
      (Fintype.card ι : ℝ≥0∞) / p ^ a := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : a ≠ 0)
  have hsubset : {ω | a + 1 ≤ ramifiedMaximum e (fun i => v i ω)} ⊆
      ⋃ i, {ω | e i * a + 1 ≤ v i ω} := by
    intro ω hω
    obtain ⟨i, -, hi⟩ := (Finset.le_sup_iff (by omega : 0 < a + 1)).mp hω
    apply Set.mem_iUnion.mpr
    refine ⟨i, ?_⟩
    change e i * a + 1 ≤ v i ω
    by_contra hn
    have hvle : v i ω ≤ e i * a := by omega
    have hh := (ceilDiv_le_iff_le_mul (he i)).mpr hvle
    change a + 1 ≤ v i ω ⌈/⌉ e i at hi
    omega
  calc
    _ ≤ μ (⋃ i, {ω | e i * a + 1 ≤ v i ω}) := measure_mono hsubset
    _ ≤ ∑ i, μ {ω | e i * a + 1 ≤ v i ω} := measure_iUnion_fintype_le μ _
    _ ≤ ∑ _i : ι, p⁻¹ ^ (a + 1) := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [ceilDiv_ramification_succ _ _ (he i)] using
        htail i (e i * a + 1) (by omega)
    _ = (Fintype.card ι : ℝ≥0∞) / p ^ (a + 1) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        div_eq_mul_inv, ENNReal.inv_pow]

 
theorem normExponent_le_degree_mul_maximum {ι : Type*} [Fintype ι]
    (e f v : ι → ℕ) (he : ∀ i, 0 < e i) :
    ∑ i, f i * v i ≤ (∑ i, f i * e i) * ramifiedMaximum e v := by
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  rw [mul_assoc]
  apply Nat.mul_le_mul_left
  calc
    v i ≤ e i * (v i ⌈/⌉ e i) := le_smul_ceilDiv (he i)
    _ ≤ e i * ramifiedMaximum e v :=
      Nat.mul_le_mul_left _ (Finset.le_sup (f := fun j => v j ⌈/⌉ e j) (Finset.mem_univ i))

lemma card_le_localDegree {ι : Type*} [Fintype ι]
    (e f : ι → ℕ) (he : ∀ i, 0 < e i) (hf : ∀ i, 0 < f i) :
    Fintype.card ι ≤ ∑ i, f i * e i := by
  calc
    Fintype.card ι = ∑ _i : ι, 1 := by simp
    _ ≤ ∑ i, f i * e i := by
      apply Finset.sum_le_sum
      intro i _
      exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (Nat.ne_of_gt (hf i)) (Nat.ne_of_gt (he i)))

 

theorem local_norm_moment_of_valuation_tails {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (e f : ι → ℕ) (he : ∀ i, 0 < e i) (hf : ∀ i, 0 < f i)
    (n : ℕ) (hn : 0 < n) (hdegree : ∑ i, f i * e i = n)
    (v : ι → Ω → ℕ) (hv : ∀ i, Measurable (v i)) (p : ℝ) (hp : 2 ≤ p)
    (htail : ∀ i k, 1 ≤ k → μ {ω | k ≤ v i ω} ≤
      (ENNReal.ofReal p)⁻¹ ^ (k ⌈/⌉ e i)) :
    (∫⁻ ω, ((ENNReal.ofReal p) ^ (∑ i, f i * v i ω)) ^ (1 / (2 * (n : ℝ))) ∂μ) ≤
      1 + (n : ℝ≥0∞) * ENNReal.ofReal (4 / Real.sqrt p) := by
  have hp0 : 0 < p := by linarith
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have hs : 0 ≤ (1 / (2 * (n : ℝ))) := by positivity
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    exact_mod_cast ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ p by linarith)
  let J : Ω → ℕ := fun ω => ramifiedMaximum e (fun i => v i ω)
  have hJ : Measurable J := ramifiedMaximum_measurable e v hv
  have hc : Fintype.card ι ≤ n := hdegree ▸ card_le_localDegree e f he hf
  have hJtail : ∀ a : ℕ, 1 ≤ a → μ {ω | a ≤ J ω} ≤
      (n : ℝ≥0∞) / (ENNReal.ofReal p) ^ a := by
    intro a ha
    apply (ramifiedMaximum_tail μ e he v (ENNReal.ofReal p) htail a ha).trans
    exact ENNReal.div_le_div (by exact_mod_cast hc) le_rfl
  calc
    _ ≤ ∫⁻ ω, (ENNReal.ofReal (Real.sqrt p)) ^ J ω ∂μ := by
      apply lintegral_mono
      intro ω
      have hnorm : ∑ i, f i * v i ω ≤ n * J ω := by
        simpa only [hdegree] using normExponent_le_degree_mul_maximum e f (fun i => v i ω) he
      calc
        _ ≤ ((ENNReal.ofReal p) ^ (n * J ω)) ^ (1 / (2 * (n : ℝ))) :=
          ENNReal.rpow_le_rpow (pow_le_pow_right₀ hp1 hnorm) hs
        _ = (ENNReal.ofReal (Real.sqrt p)) ^ J ω := by
          rw [← ENNReal.rpow_natCast_mul]
          have hexp : ((n * J ω : ℕ) : ℝ) * (1 / (2 * (n : ℝ))) = (1 / 2 : ℝ) * J ω := by
            push_cast
            field_simp
          rw [hexp, ENNReal.rpow_mul_natCast, ENNReal.ofReal_rpow_of_pos hp0,
            ← Real.sqrt_eq_rpow]
    _ ≤ _ := local_sqrt_moment μ J hJ n p hp hJtail

end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_LocalMoments
attribute [-instance] _root_.HilbertRamification.Dedekind.basePrime_isPrime _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_finite_residue _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.xMeasurableSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedMaximalIdeal.instIsMaximal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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
namespace PrimeDegreePackets
open MeasureTheory Set IsDiscreteValuationRing
open scoped ENNReal BigOperators

 

theorem saturated_local_norm_moment (p : ℕ) [Fact p.Prime]
    {ι : Type*} [Fintype ι] (R : ι → Type*)
    [∀ i, CommRing (R i)] [∀ i, IsDomain (R i)]
    [∀ i, IsDiscreteValuationRing (R i)] [∀ i, Algebra (PadicInt p) (R i)]
    [∀ i, TopologicalSpace (R i)] [∀ i, IsTopologicalRing (R i)]
    [∀ i, CompactSpace (R i)] [∀ i, T2Space (R i)]
    {A : Type*} [AddGroup A] [TopologicalSpace A] [MeasurableSpace A]
    [OpensMeasurableSpace A] [MeasurableAdd A]
    (μ : Measure A) [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]
    (φ : ∀ i, A →+ R i) (hφ : ∀ i, Continuous (φ i))
    (hsat : ∀ i, Ideal.span (Set.range (φ i)) = ⊤)
    (e f : ι → ℕ) (he0 : ∀ i, 0 < e i) (hf0 : ∀ i, 0 < f i)
    (he : ∀ i, addVal (R i) (algebraMap (PadicInt p) (R i) p) = e i)
    (n : ℕ) (hn : 0 < n) (hdegree : ∑ i, f i * e i = n) :
    (∫⁻ x, ((p : ℝ≥0∞) ^ (∑ i, f i * (addVal (R i) (φ i x)).toNat)) ^
      (1 / (2 * (n : ℝ))) ∂μ) ≤
      1 + (n : ℝ≥0∞) * ENNReal.ofReal (4 / Real.sqrt p) := by
  have hM (i : ι) (k : ℕ) :
      MeasurableSet {x | φ i x ∈ IsLocalRing.maximalIdeal (R i) ^ k} :=
    ((IsLocalRing.isOpen_maximalIdeal_pow (R i) k).preimage (hφ i)).measurableSet
  have htail (i : ι) (k : ℕ) (_hk : 1 ≤ k) :
      μ {x | k ≤ (addVal (R i) (φ i x)).toNat} ≤
        (ENNReal.ofReal (p : ℝ))⁻¹ ^ (k ⌈/⌉ e i) := by
    simpa only [ENNReal.ofReal_natCast, ENNReal.inv_pow] using
      haar_natVal_projection_tail p μ (φ i) (hsat i) (e i) (he0 i) (he i) k (hM i k)
  have hp : (2 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).two_le
  simpa only [ENNReal.ofReal_natCast] using
    local_norm_moment_of_valuation_tails μ e f he0 hf0 n hn hdegree
      (fun i x => (addVal (R i) (φ i x)).toNat)
      (fun i => measurable_dvr_natVal (hφ i)) p hp htail



end PrimeDegreePackets


namespace PrimeDegreePackets

 
theorem haar_submodule_eq_inv_cardQuot {R A : Type*} [Ring R] [AddCommGroup A]
    [Module R A] [MeasurableSpace A] [MeasurableAdd A]
    (μ : Measure A) [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]
    (L : Submodule R A) [Finite (A ⧸ L)] (hL : MeasurableSet (L : Set A)) :
    μ (L : Set A) = (L.cardQuot : ℝ≥0∞)⁻¹ := by
  have : L.toAddSubgroup.FiniteIndex :=
    @AddSubgroup.finiteIndex_of_finite_quotient _ _ _
      (inferInstanceAs (Finite (A ⧸ L)))
  have hc : (L.cardQuot : ℝ≥0∞) ≠ 0 := by
    rw [Submodule.cardQuot_apply]
    exact_mod_cast Nat.card_pos.ne'
  rw [← one_div (L.cardQuot : ℝ≥0∞)]
  apply (ENNReal.eq_div_iff hc (by simp)).mpr
  exact L.toAddSubgroup.index_mul_measure hL μ |>.trans (by simp)

section
variable {R A : Type*} [Ring R] [AddCommGroup A] [Module R A]
    [MeasurableSpace A] [MeasurableAdd A]
    (μ : Measure A) [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]
    (L : Submodule R A) [Finite (A ⧸ L)]


lemma normalizedSubmoduleHaar_probability (hL : MeasurableSet (L : Set A)) :
    IsProbabilityMeasure (normalizedSubmoduleHaar μ L) := by
  constructor
  have hemb : MeasurableEmbedding ((↑) : L → A) :=
    MeasurableEmbedding.subtype_coe hL
  have hcmap : (μ.comap ((↑) : L → A)) univ = μ (L : Set A) := by
    rw [hemb.comap_apply]
    congr 1
    ext x
    simp
  rw [normalizedSubmoduleHaar, Measure.smul_apply, hcmap, smul_eq_mul,
    haar_submodule_eq_inv_cardQuot μ L hL]
  have hc : (L.cardQuot : ℝ≥0∞) ≠ 0 := by
    rw [Submodule.cardQuot_apply]
    exact_mod_cast Nat.card_pos.ne'
  exact ENNReal.mul_inv_cancel hc (by simp)

omit [IsProbabilityMeasure μ] [Finite (A ⧸ L)] in
lemma normalizedSubmoduleHaar_leftInvariant (hL : MeasurableSet (L : Set A)) :
    (normalizedSubmoduleHaar μ L).IsAddLeftInvariant := by
  let : MeasurableAdd L := {
    measurable_const_add := fun c => ((measurable_const_add (c : A)).comp measurable_subtype_coe).subtype_mk
    measurable_add_const := fun c => ((measurable_add_const (c : A)).comp measurable_subtype_coe).subtype_mk }
  have : (μ.comap L.subtype.toAddMonoidHom).IsAddLeftInvariant :=
    Measure.IsAddLeftInvariant.comap μ (MeasurableEmbedding.subtype_coe hL)
  exact isAddLeftInvariant_smul (μ := μ.comap L.subtype.toAddMonoidHom) _

omit [MeasurableAdd A] [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant] [Finite (A ⧸ L)] in
lemma lintegral_normalizedSubmoduleHaar (hL : MeasurableSet (L : Set A))
    (F : A → ℝ≥0∞) :
    ∫⁻ x : L, F x ∂normalizedSubmoduleHaar μ L =
      (L.cardQuot : ℝ≥0∞) * ∫⁻ x in (L : Set A), F x ∂μ := by
  have he : (∫⁻ x : L, F x ∂μ.comap ((↑) : L → A)) =
      ∫⁻ x in (L : Set A), F x ∂μ := lintegral_subtype_comap hL F
  rw [normalizedSubmoduleHaar, lintegral_smul_measure, he, smul_eq_mul]

omit [MeasurableAdd A] [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant] in
lemma ambient_lintegral_eq_normalized (hL : MeasurableSet (L : Set A))
    (F : A → ℝ≥0∞) :
    ∫⁻ x in (L : Set A), F x ∂μ =
      (L.cardQuot : ℝ≥0∞)⁻¹ * ∫⁻ x : L, F x ∂normalizedSubmoduleHaar μ L := by
  rw [lintegral_normalizedSubmoduleHaar μ L hL F, ← mul_assoc]
  have hc : (L.cardQuot : ℝ≥0∞) ≠ 0 := by
    rw [Submodule.cardQuot_apply]
    exact_mod_cast Nat.card_pos.ne'
  rw [ENNReal.inv_mul_cancel hc (by simp), one_mul]

end
end PrimeDegreePackets


namespace PrimeDegreePackets
open MeasureTheory Set IsDiscreteValuationRing
open scoped ENNReal BigOperators

lemma projection_saturation {ι : Type*} (R : ι → Type*) [∀ i, CommRing (R i)]
    (p : ℕ) [Fact p.Prime] [∀ i, Algebra (PadicInt p) (R i)]
    (L : Submodule (PadicInt p) (∀ i, R i))
    (hsat : Ideal.span (L : Set (∀ i, R i)) = ⊤) (i : ι) :
    Ideal.span (Set.range (((Pi.evalRingHom R i).toAddMonoidHom).comp L.subtype.toAddMonoidHom)) = ⊤ := by
  have hmap := congrArg (Ideal.map (Pi.evalRingHom R i)) hsat
  rw [Ideal.map_span, Ideal.map_top] at hmap
  convert hmap using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ext x
  simp only [Set.mem_range, Set.mem_image, AddMonoidHom.comp_apply,
    Pi.evalRingHom_apply]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, y.property, hy⟩
  · rintro ⟨y, hy, hyx⟩
    exact ⟨⟨y, hy⟩, hyx⟩

end PrimeDegreePackets


namespace PrimeDegreePackets
open MeasureTheory Set IsDiscreteValuationRing
open scoped ENNReal BigOperators

 

theorem finite_index_saturated_module_norm_moment (p : ℕ) [Fact p.Prime]
    {ι : Type*} [Fintype ι] (R : ι → Type*)
    [∀ i, CommRing (R i)] [∀ i, IsDomain (R i)]
    [∀ i, IsDiscreteValuationRing (R i)] [∀ i, Algebra (PadicInt p) (R i)]
    [∀ i, TopologicalSpace (R i)] [∀ i, IsTopologicalRing (R i)]
    [∀ i, CompactSpace (R i)] [∀ i, T2Space (R i)]
    [∀ i, MeasurableSpace (R i)] [∀ i, BorelSpace (R i)]
    [∀ i, SecondCountableTopology (R i)]
    (μ : Measure (∀ i, R i)) [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]
    (L : Submodule (PadicInt p) (∀ i, R i)) [Finite ((∀ i, R i) ⧸ L)]
    (hL : MeasurableSet (L : Set (∀ i, R i)))
    (hsat : Ideal.span (L : Set (∀ i, R i)) = ⊤)
    (e f : ι → ℕ) (he0 : ∀ i, 0 < e i) (hf0 : ∀ i, 0 < f i)
    (he : ∀ i, addVal (R i) (algebraMap (PadicInt p) (R i) p) = e i)
    (n : ℕ) (hn : 0 < n) (hdegree : ∑ i, f i * e i = n) :
    (∫⁻ x in (L : Set (∀ i, R i)), ((p : ℝ≥0∞) ^
       (∑ i, f i * (addVal (R i) (x i)).toNat)) ^ (1 / (2 * (n : ℝ))) ∂μ) ≤
      (L.cardQuot : ℝ≥0∞)⁻¹ *
        (1 + (n : ℝ≥0∞) * ENNReal.ofReal (4 / Real.sqrt p)) := by
  let ν := normalizedSubmoduleHaar μ L
  let : IsProbabilityMeasure ν := normalizedSubmoduleHaar_probability μ L hL
  let : ν.IsAddLeftInvariant := normalizedSubmoduleHaar_leftInvariant μ L hL
  let : MeasurableAdd L := {
    measurable_const_add := fun c => ((measurable_const_add (c : ∀ i, R i)).comp measurable_subtype_coe).subtype_mk
    measurable_add_const := fun c => ((measurable_add_const (c : ∀ i, R i)).comp measurable_subtype_coe).subtype_mk }
  rw [ambient_lintegral_eq_normalized μ L hL]
  apply mul_le_mul_right
  exact saturated_local_norm_moment p R ν
    (fun i => (Pi.evalRingHom R i).toAddMonoidHom.comp L.subtype.toAddMonoidHom)
    (fun i => (continuous_apply i).comp continuous_subtype_val)
    (projection_saturation R p L hsat)
    e f he0 hf0 he n hn hdegree

end PrimeDegreePackets

open MeasureTheory Set IsDiscreteValuationRing
namespace PrimeDegreePackets

section DVR
variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [MeasurableSpace R] [MeasurableAdd R]
    [Finite (IsLocalRing.ResidueField R)]
    (μ : Measure R) [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]

 
theorem haar_dvr_ideal_pow (k : ℕ)
    (hM : MeasurableSet ((IsLocalRing.maximalIdeal R ^ k : Ideal R) : Set R)) :
    μ ((IsLocalRing.maximalIdeal R ^ k : Ideal R) : Set R) =
      ((Nat.card (IsLocalRing.ResidueField R) : ℝ≥0∞) ^ k)⁻¹ := by
  have : Finite (R ⧸ IsLocalRing.maximalIdeal R ^ k) :=
    IsLocalRing.finite_quotient_iff.mpr ⟨k, le_rfl⟩
  rw [haar_submodule_eq_inv_cardQuot μ _ hM, cardQuot_pow_of_prime]
  · rw [Nat.cast_pow]
    rfl
  · exact fun h => IsDiscreteValuationRing.not_isField R
      (IsLocalRing.isField_iff_maximalIdeal_eq.mpr h)

omit [MeasurableSpace R] [MeasurableAdd R] [Finite (IsLocalRing.ResidueField R)] in
 
lemma dvr_shell_eq_sdiff (k : ℕ) :
    {x : R | addVal R x = k} =
      ((IsLocalRing.maximalIdeal R ^ k : Ideal R) : Set R) \
      ((IsLocalRing.maximalIdeal R ^ (k + 1) : Ideal R) : Set R) := by
  ext x
  simp only [Set.mem_sdiff, SetLike.mem_coe, mem_ofPred_eq, mem_maximalIdeal_pow_iff_addVal]
  induction addVal R x using ENat.recTopCoe with
  | top => simp
  | coe v => simp only [ENat.natCast_le_natCast, ENat.natCast_inj]; omega

 
theorem haar_dvr_shell (k : ℕ)
    (hM : ∀ k : ℕ, MeasurableSet ((IsLocalRing.maximalIdeal R ^ k : Ideal R) : Set R)) :
    μ {x : R | addVal R x = k} =
      (1 - (Nat.card (IsLocalRing.ResidueField R) : ℝ≥0∞)⁻¹) /
      (Nat.card (IsLocalRing.ResidueField R) : ℝ≥0∞) ^ k := by
  have hsub : ((IsLocalRing.maximalIdeal R ^ (k + 1) : Ideal R) : Set R) ⊆
      ((IsLocalRing.maximalIdeal R ^ k : Ideal R) : Set R) := by
    intro x hx
    change x ∈ IsLocalRing.maximalIdeal R ^ (k + 1) at hx
    change x ∈ IsLocalRing.maximalIdeal R ^ k
    rw [mem_maximalIdeal_pow_iff_addVal] at hx ⊢
    exact (ENat.natCast_le_natCast.mpr (Nat.le_succ k)).trans hx
  have hq : (Nat.card (IsLocalRing.ResidueField R) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  rw [dvr_shell_eq_sdiff, measure_sdiff hsub (hM _).nullMeasurableSet (measure_ne_top μ _),
    haar_dvr_ideal_pow μ k (hM k), haar_dvr_ideal_pow μ (k + 1) (hM _),
    pow_succ, ENNReal.mul_inv (by simp) (by simp [hq]), div_eq_mul_inv, ENNReal.sub_mul (by simp [hq])]
  simp [mul_comm]

end DVR
end PrimeDegreePackets


namespace PrimeDegreePackets

section Algebra
variable {ι : Type*} (R : ι → Type*) [∀ i, CommRing (R i)]
    [∀ i, IsDomain (R i)] [∀ i, IsDiscreteValuationRing (R i)]


lemma productDVRShell_eq_pi (k : ι → ℕ) :
    productDVRShell R k = Set.univ.pi (fun i => {x : R i | addVal (R i) x = k i}) := by
  ext x
  simp [productDVRShell]

lemma productDVRShell_smul_iff (k : ι → ℕ) (u : (∀ i, R i)ˣ) (x : ∀ i, R i) :
    u • x ∈ productDVRShell R k ↔ x ∈ productDVRShell R k := by
  have hu (i : ι) : addVal (R i) (u.val i) = 0 :=
    addVal_eq_zero_of_unit (MulEquiv.piUnits u i)
  change (∀ i, addVal (R i) (u.val i * x i) = k i) ↔ _
  simp only [addVal_mul, hu, zero_add]
  rfl

lemma productDVRShell_transitive (k : ι → ℕ) {x y : ∀ i, R i}
    (hx : x ∈ productDVRShell R k) (hy : y ∈ productDVRShell R k) :
    ∃ u : (∀ i, R i)ˣ, u • x = y := by
  have h (i : ι) : Associated (x i) (y i) :=
    (addVal_eq_iff_associated _ _).mp ((hx i).trans (hy i).symm)
  choose u hu using h
  refine ⟨MulEquiv.piUnits.symm u, ?_⟩
  funext i
  change (u i : R i) * x i = y i
  simpa only [mul_comm] using hu i

lemma productDVRShell_pairwiseDisjoint : Pairwise (fun k l => Disjoint (productDVRShell R k) (productDVRShell R l)) := by
  intro k l hkl
  apply Set.disjoint_left.mpr
  intro x hx hl
  apply hkl
  funext i
  exact ENat.natCast_inj.mp ((hx i).symm.trans (hl i))

lemma mem_iUnion_productDVRShell_iff (x : ∀ i, R i) :
    x ∈ ⋃ k : ι → ℕ, productDVRShell R k ↔ ∀ i, x i ≠ 0 := by
  simp only [mem_iUnion]
  constructor
  · rintro ⟨k, hk⟩ i hi
    have := hk i
    rw [hi, addVal_zero] at this
    exact ENat.top_ne_natCast (k i) this
  · intro hx
    refine ⟨fun i => (addVal (R i) (x i)).toNat, ?_⟩
    intro i
    exact (ENat.natCast_toNat (fun h => hx i (addVal_eq_top_iff.mp h))).symm

end Algebra

section Measurability
variable {ι : Type*} [Fintype ι] (R : ι → Type*)
    [∀ i, CommRing (R i)] [∀ i, IsDomain (R i)] [∀ i, IsDiscreteValuationRing (R i)]
    [∀ i, TopologicalSpace (R i)] [∀ i, IsTopologicalRing (R i)]
    [∀ i, CompactSpace (R i)] [∀ i, T2Space (R i)]
    [∀ i, MeasurableSpace (R i)] [∀ i, BorelSpace (R i)]

omit [Fintype ι] in
lemma measurableSet_dvr_shell (i : ι) (k : ℕ) :
    MeasurableSet {x : R i | addVal (R i) x = k} := by
  have hset : {x : R i | addVal (R i) x = k} =
      ((IsLocalRing.maximalIdeal (R i) ^ k : Ideal (R i)) : Set (R i)) \
      ((IsLocalRing.maximalIdeal (R i) ^ (k + 1) : Ideal (R i)) : Set (R i)) := by
    ext x
    simp only [Set.mem_sdiff, SetLike.mem_coe, mem_ofPred_eq, mem_maximalIdeal_pow_iff_addVal]
    induction addVal (R i) x using ENat.recTopCoe with
    | top => simp
    | coe v => simp only [ENat.natCast_le_natCast, ENat.natCast_inj]; omega
  rw [hset]
  exact (IsLocalRing.isOpen_maximalIdeal_pow (R i) k).measurableSet.diff
    (IsLocalRing.isOpen_maximalIdeal_pow (R i) (k + 1)).measurableSet

lemma measurableSet_productDVRShell (k : ι → ℕ) : MeasurableSet (productDVRShell R k) := by
  rw [productDVRShell_eq_pi]
  exact MeasurableSet.univ_pi (fun i => measurableSet_dvr_shell R i (k i))

end Measurability
end PrimeDegreePackets


namespace PrimeDegreePackets
open MeasureTheory Set IsDiscreteValuationRing
open scoped ENNReal BigOperators
section
variable {ι : Type*} [Fintype ι] (R : ι → Type*)
    [∀ i, CommRing (R i)] [∀ i, IsDomain (R i)] [∀ i, IsDiscreteValuationRing (R i)]
    [∀ i, TopologicalSpace (R i)] [∀ i, IsTopologicalRing (R i)]
    [∀ i, CompactSpace (R i)] [∀ i, T2Space (R i)]
    [∀ i, MeasurableSpace (R i)] [∀ i, BorelSpace (R i)]

lemma product_shell_mass
    (μ : ∀ i, Measure (R i)) [∀ i, IsProbabilityMeasure (μ i)]
    [∀ i, (μ i).IsAddLeftInvariant] (k : ι → ℕ) :
    Measure.pi μ (productDVRShell R k) = localZinv R / shellNorm R k := by
  rw [productDVRShell_eq_pi, Measure.pi_pi]
  have hM (i : ι) (j : ℕ) :
      MeasurableSet ((IsLocalRing.maximalIdeal (R i) ^ j : Ideal (R i)) : Set (R i)) :=
    (IsLocalRing.isOpen_maximalIdeal_pow (R i) j).measurableSet
  simp_rw [haar_dvr_shell _ _ (hM _)]
  exact ENNReal.prod_div_distrib_of_ne_top (by simp)

omit [∀ i, BorelSpace (R i)] [∀ i, MeasurableSpace (R i)] in
lemma localZinv_ne_zero : localZinv R ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  have hq : (1 : ℝ≥0∞) < Nat.card (IsLocalRing.ResidueField (R i)) := by
    let := Fintype.ofFinite (IsLocalRing.ResidueField (R i))
    rw [Nat.card_eq_fintype_card]
    exact_mod_cast (Fintype.one_lt_card : 1 < Fintype.card (IsLocalRing.ResidueField (R i)))
  apply ne_of_gt
  exact tsub_pos_iff_lt.mpr (ENNReal.inv_lt_one.mpr hq)

omit [∀ i, IsTopologicalRing (R i)] [∀ i, CompactSpace (R i)]
    [∀ i, T2Space (R i)] [∀ i, BorelSpace (R i)]
    [∀ i, TopologicalSpace (R i)] [∀ i, MeasurableSpace (R i)] in
lemma localZinv_ne_top : localZinv R ≠ ∞ := by
  apply ENNReal.prod_ne_top
  intro i _
  exact ne_of_lt ((tsub_le_self).trans_lt (by simp))

omit [∀ i, BorelSpace (R i)] [∀ i, MeasurableSpace (R i)] in
lemma shellNorm_ne_zero (k : ι → ℕ) : shellNorm R k ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  apply pow_ne_zero
  exact_mod_cast (Nat.card_pos : 0 < Nat.card (IsLocalRing.ResidueField (R i))).ne'

omit [∀ i, IsTopologicalRing (R i)] [∀ i, CompactSpace (R i)]
    [∀ i, T2Space (R i)] [∀ i, BorelSpace (R i)]
    [∀ i, TopologicalSpace (R i)] [∀ i, MeasurableSpace (R i)] in
lemma shellNorm_ne_top (k : ι → ℕ) : shellNorm R k ≠ ∞ := by
  apply ENNReal.prod_ne_top
  intro i _
  exact ENNReal.pow_ne_top (by simp)

omit [∀ i, IsTopologicalRing (R i)] [∀ i, CompactSpace (R i)]
    [∀ i, T2Space (R i)] [∀ i, BorelSpace (R i)]
    [∀ i, TopologicalSpace (R i)] [∀ i, MeasurableSpace (R i)] in
lemma shellNorm_eq_prime_pow (p : ℕ) (f k : ι → ℕ)
    (hcard : ∀ i, Nat.card (IsLocalRing.ResidueField (R i)) = p ^ f i) :
    shellNorm R k = (p : ℝ≥0∞) ^ (∑ i, f i * k i) := by
  simp only [shellNorm, hcard, Nat.cast_pow, ← pow_mul]
  exact Finset.prod_pow_eq_pow_sum Finset.univ (fun i => f i * k i) (p : ℝ≥0∞)

end
end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_OrbitProbability
attribute [-instance] _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.diagonalLogAction_continuous _root_.OAI.PrimeDegreePackets.gSecondCountable _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.OAI.PrimeDegreePackets.xSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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
namespace PrimeDegreePackets
open MeasureTheory Set IsDiscreteValuationRing Filter
open scoped ENNReal

 
theorem haar_dvr_zero {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Finite (IsLocalRing.ResidueField R)]
    [MeasurableSpace R] [MeasurableAdd R]
    (μ : Measure R) [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]
    (hM : ∀ k : ℕ, MeasurableSet ((IsLocalRing.maximalIdeal R ^ k : Ideal R) : Set R)) :
    μ {0} = 0 := by
  let := Fintype.ofFinite (IsLocalRing.ResidueField R)
  have hq : (1 : ℝ≥0∞) < Nat.card (IsLocalRing.ResidueField R) := by
    rw [Nat.card_eq_fintype_card]
    exact_mod_cast (Fintype.one_lt_card : 1 < Fintype.card (IsLocalRing.ResidueField R))
  have hlim := ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (ENNReal.inv_lt_one.mpr hq)
  apply le_antisymm _ zero_le
  apply ge_of_tendsto' hlim
  intro k
  calc
    μ {0} ≤ μ ((IsLocalRing.maximalIdeal R ^ k : Ideal R) : Set R) := by
      apply measure_mono
      intro x hx
      simp only [mem_singleton_iff] at hx
      simp [hx]
    _ = _ := by rw [haar_dvr_ideal_pow μ k (hM k), ENNReal.inv_pow]

end PrimeDegreePackets


namespace PrimeDegreePackets

section Action
variable {G X : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
    [MeasurableSpace X] [MulAction G X] [MeasurableSMul₂ G X]
    (ν : Measure G) [IsProbabilityMeasure ν] [ν.IsMulRightInvariant]



omit [MeasurableSpace X] [MeasurableSMul₂ G X] [IsProbabilityMeasure ν] in
lemma orbitContainmentProbability_smul (L : Set X) (x : X) (g : G) :
    orbitContainmentProbability ν L (g • x) = orbitContainmentProbability ν L x := by
  unfold orbitContainmentProbability
  simp_rw [← mul_smul]
  exact lintegral_mul_right_eq_self (fun h => L.indicator (fun _ => (1 : ℝ≥0∞)) (h • x)) g

 

theorem orbitContainmentProbability_mul_shell_measure
    (μ : Measure X) [IsFiniteMeasure μ] [SMulInvariantMeasure G X μ]
    (S L : Set X) (hS : MeasurableSet S) (hL : MeasurableSet L)
    (hinv : ∀ (g : G) (x : X), g • x ∈ S ↔ x ∈ S)
    (x₀ : X) (htrans : ∀ x ∈ S, ∃ g : G, g • x₀ = x) :
    orbitContainmentProbability ν L x₀ * μ S = μ (L ∩ S) := by
  have hconstant (x : X) (hx : x ∈ S) :
      orbitContainmentProbability ν L x = orbitContainmentProbability ν L x₀ := by
    obtain ⟨g, rfl⟩ := htrans x hx
    exact orbitContainmentProbability_smul ν L x₀ g
  have hfun : Measurable (fun (z : X × G) =>
      L.indicator (fun _ => (1 : ℝ≥0∞)) (z.2 • z.1)) :=
    (measurable_const.indicator hL).comp (measurable_snd.smul measurable_fst)
  calc
    orbitContainmentProbability ν L x₀ * μ S =
        ∫⁻ x in S, orbitContainmentProbability ν L x ∂μ := by
      rw [← setLIntegral_const]
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem hS] with x hx
      exact (hconstant x hx).symm
    _ = ∫⁻ g, ∫⁻ x in S, L.indicator (fun _ => (1 : ℝ≥0∞)) (g • x) ∂μ ∂ν :=
      lintegral_lintegral_swap hfun.aemeasurable
    _ = ∫⁻ _g, μ (L ∩ S) ∂ν := by
      apply lintegral_congr
      intro g
      have heq : (fun x => L.indicator (fun _ => (1 : ℝ≥0∞)) (g • x)) =
          ((g • ·) ⁻¹' L).indicator (fun _ => (1 : ℝ≥0∞)) := by
        ext x
        rfl
      rw [heq, show (fun _ : X => (1 : ℝ≥0∞)) = (1 : X → ℝ≥0∞) from rfl,
        lintegral_indicator_one (hL.preimage (measurable_const_smul g)),
        Measure.restrict_apply (hL.preimage (measurable_const_smul g))]
      have hset : (g • ·) ⁻¹' L ∩ S = (g • ·) ⁻¹' (L ∩ S) := by
        ext x
        simp only [mem_inter_iff, mem_preimage, hinv]
      rw [hset, measure_preimage_smul]
    _ = μ (L ∩ S) := by simp

end Action
end PrimeDegreePackets


namespace PrimeDegreePackets

 

theorem lintegral_eq_tsum_shells {X κ : Type*} [MeasurableSpace X] [Countable κ]
    (μ : Measure X) (S : κ → Set X) (hS : ∀ k, MeasurableSet (S k))
    (hdisj : Pairwise (fun k l => Disjoint (S k) (S l)))
    (hfull : μ (⋃ k, S k)ᶜ = 0)
    (F : X → ℝ≥0∞) (w : κ → ℝ≥0∞) (hF : ∀ k x, x ∈ S k → F x = w k) :
    ∫⁻ x, F x ∂μ = ∑' k, w k * μ (S k) := by
  have hae : ∀ᵐ x ∂μ, x ∈ ⋃ k, S k := by
    rw [ae_iff]
    exact hfull
  calc
    _ = ∫⁻ x in ⋃ k, S k, F x ∂μ := by
      rw [Measure.restrict_eq_self_of_ae_mem hae]
    _ = ∑' k, ∫⁻ x in S k, F x ∂μ := lintegral_iUnion hS hdisj F
    _ = _ := by
      apply tsum_congr
      intro k
      rw [← setLIntegral_const]
      apply setLIntegral_congr_fun (hS k)
      exact hF k

 
theorem restricted_lintegral_eq_tsum_shells {X κ : Type*}
    [MeasurableSpace X] [Countable κ]
    (μ : Measure X) (S : κ → Set X) (hS : ∀ k, MeasurableSet (S k))
    (hdisj : Pairwise (fun k l => Disjoint (S k) (S l)))
    (hfull : μ (⋃ k, S k)ᶜ = 0)
    (L : Set X) (F : X → ℝ≥0∞) (w : κ → ℝ≥0∞)
    (hF : ∀ k x, x ∈ S k → F x = w k) :
    ∫⁻ x in L, F x ∂μ = ∑' k, w k * μ (L ∩ S k) := by
  have hr : (μ.restrict L) (⋃ k, S k)ᶜ = 0 :=
    le_antisymm ((Measure.restrict_le_self (μ := μ) (s := L) _).trans hfull.le) zero_le
  have he := lintegral_eq_tsum_shells (μ.restrict L) S hS hdisj hr F w hF
  simpa only [Measure.restrict_apply (hS _), inter_comm] using he

end PrimeDegreePackets


namespace PrimeDegreePackets

lemma units_smulInvariant_addHaar {R : Type*} [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [CompactSpace R]
    [MeasurableSpace R] [BorelSpace R]
    (μ : Measure R) [μ.IsAddHaarMeasure] : SMulInvariantMeasure Rˣ R μ := by
  constructor
  intro u S hS
  let f : R ≃ₗ[R] R := LinearEquiv.smulOfUnit u
  have hf : MeasurePreserving f μ μ :=
    f.toAddMonoidHom.measurePreserving (by
      change Continuous (fun x : R => (u : R) * x)
      fun_prop) f.surjective rfl
  exact hf.measure_preimage hS.nullMeasurableSet

end PrimeDegreePackets


namespace PrimeDegreePackets
open MeasureTheory Set IsDiscreteValuationRing
open scoped ENNReal BigOperators
section
variable {ι : Type*} [Fintype ι] (R : ι → Type*)
    [∀ i, CommRing (R i)] [∀ i, IsDomain (R i)] [∀ i, IsDiscreteValuationRing (R i)]
    [∀ i, TopologicalSpace (R i)] [∀ i, IsTopologicalRing (R i)]
    [∀ i, CompactSpace (R i)] [∀ i, T2Space (R i)]
    [∀ i, MeasurableSpace (R i)] [∀ i, BorelSpace (R i)]

lemma productDVRShell_full_measure
    (μ : ∀ i, Measure (R i)) [∀ i, IsProbabilityMeasure (μ i)]
    [∀ i, (μ i).IsAddLeftInvariant] :
    Measure.pi μ (⋃ k : ι → ℕ, productDVRShell R k)ᶜ = 0 := by
  have hzero (i : ι) : μ i {0} = 0 :=
    haar_dvr_zero (μ i) (fun k => (IsLocalRing.isOpen_maximalIdeal_pow (R i) k).measurableSet)
  have hnull (i : ι) : Measure.pi μ {x : ∀ i, R i | x i = 0} = 0 :=
    Measure.pi_eval_preimage_null μ (hzero i)
  have hset : (⋃ k : ι → ℕ, productDVRShell R k)ᶜ = ⋃ i, {x : ∀ i, R i | x i = 0} := by
    ext x
    rw [mem_compl_iff, mem_iUnion_productDVRShell_iff R x]
    simp
  rw [hset]
  exact measure_iUnion_null hnull



end
end PrimeDegreePackets


namespace PrimeDegreePackets
open MeasureTheory Set IsDiscreteValuationRing
open scoped ENNReal BigOperators
section
variable {ι : Type*} [Fintype ι] (R : ι → Type*)
    [∀ i, CommRing (R i)] [∀ i, IsDomain (R i)] [∀ i, IsDiscreteValuationRing (R i)]
    [∀ i, TopologicalSpace (R i)] [∀ i, IsTopologicalRing (R i)]
    [∀ i, CompactSpace (R i)] [∀ i, T2Space (R i)]
    [∀ i, MeasurableSpace (R i)] [∀ i, BorelSpace (R i)]
    [∀ i, SecondCountableTopology (R i)]
    [MeasurableSpace (∀ i, R i)ˣ] [BorelSpace (∀ i, R i)ˣ]
    (μ : ∀ i, Measure (R i)) [∀ i, IsProbabilityMeasure (μ i)]
    [∀ i, (μ i).IsAddHaarMeasure]
    (ν : Measure (∀ i, R i)ˣ) [IsProbabilityMeasure ν] [ν.IsMulRightInvariant]

lemma localShellProbability_mul_mass (L : Set (∀ i, R i)) (hL : MeasurableSet L)
    (k : ι → ℕ) :
    localShellProbability R ν L k * (localZinv R / shellNorm R k) =
      Measure.pi μ (L ∩ productDVRShell R k) := by
  let : SMulInvariantMeasure (∀ i, R i)ˣ (∀ i, R i) (Measure.pi μ) :=
    units_smulInvariant_addHaar (Measure.pi μ)
  rw [← product_shell_mass R μ k]
  apply orbitContainmentProbability_mul_shell_measure ν (Measure.pi μ)
    (productDVRShell R k) L (measurableSet_productDVRShell R k) hL
    (productDVRShell_smul_iff R k)
  intro x hx
  exact productDVRShell_transitive R k (productDVRShell_nonempty R k).choose_spec hx

 
theorem local_weight_integral_identity (L : Set (∀ i, R i)) (hL : MeasurableSet L)
    (s : ℝ) :
    (∫⁻ x in L, shellNorm R (fun i => (addVal (R i) (x i)).toNat) ^ s ∂Measure.pi μ) =
      localZinv R * ∑' k : ι → ℕ,
        localShellProbability R ν L k * shellNorm R k ^ (s - 1) := by
  rw [restricted_lintegral_eq_tsum_shells (Measure.pi μ) (productDVRShell R)
    (measurableSet_productDVRShell R) (productDVRShell_pairwiseDisjoint R)
    (productDVRShell_full_measure R μ) L _ (fun k => shellNorm R k ^ s) (by
      intro k x hx
      congr 2
      funext i
      rw [hx i, ENat.toNat_natCast])]
  rw [← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro k
  rw [← localShellProbability_mul_mass R μ ν L hL k,
    ENNReal.rpow_sub s 1 (shellNorm_ne_zero R k) (shellNorm_ne_top R k),
    ENNReal.rpow_one, div_eq_mul_inv, div_eq_mul_inv]
  ac_rfl

end
end PrimeDegreePackets


namespace PrimeDegreePackets
open MeasureTheory Set IsDiscreteValuationRing
open scoped ENNReal BigOperators
section
variable {ι : Type*} [Fintype ι] (R : ι → Type*)
    [∀ i, CommRing (R i)] [∀ i, IsDomain (R i)] [∀ i, IsDiscreteValuationRing (R i)]
    [∀ i, TopologicalSpace (R i)] [∀ i, IsTopologicalRing (R i)]
    [∀ i, CompactSpace (R i)] [∀ i, T2Space (R i)]
    [∀ i, MeasurableSpace (R i)] [∀ i, BorelSpace (R i)]
    [∀ i, SecondCountableTopology (R i)]
    [MeasurableSpace (∀ i, R i)ˣ] [BorelSpace (∀ i, R i)ˣ]
    (μ : ∀ i, Measure (R i)) [∀ i, IsProbabilityMeasure (μ i)]
    [∀ i, (μ i).IsAddHaarMeasure]
    (ν : Measure (∀ i, R i)ˣ) [IsProbabilityMeasure ν] [ν.IsMulRightInvariant]

include μ in
 

theorem local_weight_moment (p : ℕ) [Fact p.Prime] [∀ i, Algebra (PadicInt p) (R i)]
    (L : Submodule (PadicInt p) (∀ i, R i)) [Finite ((∀ i, R i) ⧸ L)]
    (hL : MeasurableSet (L : Set (∀ i, R i)))
    (hsat : Ideal.span (L : Set (∀ i, R i)) = ⊤)
    (e f : ι → ℕ) (he0 : ∀ i, 0 < e i) (hf0 : ∀ i, 0 < f i)
    (he : ∀ i, addVal (R i) (algebraMap (PadicInt p) (R i) p) = e i)
    (hcard : ∀ i, Nat.card (IsLocalRing.ResidueField (R i)) = p ^ f i)
    (n : ℕ) (hn : 0 < n) (hdegree : ∑ i, f i * e i = n) :
    (∑' k : ι → ℕ,
      localShellProbability R ν L k * shellNorm R k ^ (1 / (2 * (n : ℝ)) - 1)) ≤
      (L.cardQuot : ℝ≥0∞)⁻¹ * ((localZinv R)⁻¹ *
        (1 + (n : ℝ≥0∞) * ENNReal.ofReal (4 / Real.sqrt p))) := by
  have hid := local_weight_integral_identity R μ ν L hL (1 / (2 * (n : ℝ)))
  have hmoment := finite_index_saturated_module_norm_moment p R (Measure.pi μ)
    L hL hsat e f he0 hf0 he n hn hdegree
  have hm : (∫⁻ x in (L : Set (∀ i, R i)),
      shellNorm R (fun i => (addVal (R i) (x i)).toNat) ^ (1 / (2 * (n : ℝ)))
        ∂Measure.pi μ) ≤ (L.cardQuot : ℝ≥0∞)⁻¹ *
      (1 + (n : ℝ≥0∞) * ENNReal.ofReal (4 / Real.sqrt p)) := by
    simpa only [shellNorm_eq_prime_pow R p f _ hcard] using hmoment
  have heq := (ENNReal.eq_div_iff (localZinv_ne_zero R) (localZinv_ne_top R)).mpr hid.symm
  rw [heq]
  calc
    _ ≤ ((L.cardQuot : ℝ≥0∞)⁻¹ *
      (1 + (n : ℝ≥0∞) * ENNReal.ofReal (4 / Real.sqrt p))) / localZinv R :=
      ENNReal.div_le_div hm le_rfl
    _ = _ := by simp only [div_eq_mul_inv]; ac_rfl

end
end PrimeDegreePackets

open Filter
open scoped BigOperators Topology


namespace PrimeDegreePackets

lemma localZinv_inv_le {ι : Type*} [Fintype ι] (R : ι → Type*)
    [∀ i, CommRing (R i)] [∀ i, IsDomain (R i)] [∀ i, IsDiscreteValuationRing (R i)] (p n : ℕ) (f : ι → ℕ) (hf : ∀ i, 0 < f i)
    (hcard : ∀ i, Nat.card (IsLocalRing.ResidueField (R i)) = p ^ f i)
    (hnum : Fintype.card ι ≤ n) :
    (localZinv R)⁻¹ ≤ ((1 - (p : ℝ≥0∞)⁻¹) ^ n)⁻¹ := by
  apply ENNReal.inv_le_inv.mpr
  calc
    _ ≤ (1 - (p : ℝ≥0∞)⁻¹) ^ Fintype.card ι :=
      pow_le_pow_of_le_one zero_le tsub_le_self hnum
    _ = ∏ _i : ι, (1 - (p : ℝ≥0∞)⁻¹) := by simp
    _ ≤ localZinv R := by
      apply Finset.prod_le_prod'
      intro i _
      apply tsub_le_tsub_left
      apply ENNReal.inv_le_inv.mpr
      exact_mod_cast (hcard i ▸ Nat.le_pow (hf i) : p ≤ Nat.card (IsLocalRing.ResidueField (R i)))

lemma localEulerFactor_le_majorant {ι : Type*} [Fintype ι] (R : ι → Type*)
    [∀ i, CommRing (R i)] [∀ i, IsDomain (R i)] [∀ i, IsDiscreteValuationRing (R i)] (p n : ℕ) (hp : 1 < p)
    (f : ι → ℕ) (hf : ∀ i, 0 < f i)
    (hcard : ∀ i, Nat.card (IsLocalRing.ResidueField (R i)) = p ^ f i)
    (hnum : Fintype.card ι ≤ n) :
    (localZinv R)⁻¹ * (1 + (n : ℝ≥0∞) * ENNReal.ofReal (4 / Real.sqrt p)) ≤
      ENNReal.ofReal (localMajorant n p) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp
  have hi : 0 < 1 - (p : ℝ)⁻¹ := sub_pos.mpr ((inv_lt_one₀ hp0).mpr hp1)
  have hbase : ENNReal.ofReal (1 - (p : ℝ)⁻¹) = 1 - (p : ℝ≥0∞)⁻¹ := by
    rw [ENNReal.ofReal_sub _ (by positivity), ENNReal.ofReal_one,
      ENNReal.ofReal_inv_of_pos hp0, ENNReal.ofReal_natCast]
  calc
    _ ≤ ((1 - (p : ℝ≥0∞)⁻¹) ^ n)⁻¹ *
      (1 + (n : ℝ≥0∞) * ENNReal.ofReal (4 / Real.sqrt p)) :=
        mul_le_mul_left (localZinv_inv_le R p n f hf hcard hnum) _
    _ = ENNReal.ofReal (localMajorant n p) := by
      unfold localMajorant
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_inv_of_pos (pow_pos hi n),
        ENNReal.ofReal_pow hi.le, hbase,
        ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_one]
      congr 2
      rw [show 4 * (n : ℝ) / Real.sqrt p = n * (4 / Real.sqrt p) by ring,
        ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]

end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_PrimeFactors
attribute [-instance] _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.infiniteAdeleRingT2Space
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

 

lemma local_weight_product_factorization {ι : Type u} [Fintype ι]
    (κ : ι → Type v) (P d : ∀ i, κ i → ℝ≥0∞) (s : ℝ) :
    (∑' k : ∀ i, κ i, (∏ i, P i (k i)) * (∏ i, (d i (k i)) ^ s)) =
      ∏ i, ∑' k : κ i, P i k * d i k ^ s := by
  simp_rw [← Finset.prod_mul_distrib]
  exact ennreal_tsum_fintype_prod κ (fun i x => P i x * d i x ^ s)

end PrimeDegreePackets


namespace PrimeDegreePackets
open MeasureTheory Set IsDiscreteValuationRing
open scoped ENNReal BigOperators


lemma localProductConstant_bound (n : ℕ) (ε : ℝ) (hε : 0 < ε)
    (S : Finset ℕ) (q : ℝ) (hS : ∀ p ∈ S, 1 ≤ p)
    (hq : (∏ p ∈ S, (p : ℝ)) ≤ q) :
    (∏ p ∈ S, localMajorant n p) ≤ localProductConstant n ε hε * q ^ ε :=
  (localMajorant_product_le n ε hε).choose_spec.2 S q hS hq

end PrimeDegreePackets


end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_LocalModels
attribute [-instance] _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.infiniteAdeleRingT2Space
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
open MeasureTheory Set IsDiscreteValuationRing
open scoped ENNReal BigOperators



section
variable (n : ℕ) (S : Finset ℕ) [∀ p : S, Fact p.val.Prime]
    (ι : S → Type*) [∀ p, Fintype (ι p)]
    (R : ∀ p : S, ι p → Type*)
    [∀ p i, CommRing (R p i)] [∀ p i, IsDomain (R p i)]
    [∀ p i, IsDiscreteValuationRing (R p i)]
    [∀ p i, Algebra (PadicInt p.val) (R p i)]
    [∀ p i, TopologicalSpace (R p i)] [∀ p i, IsTopologicalRing (R p i)]
    [∀ p i, CompactSpace (R p i)] [∀ p i, T2Space (R p i)]
    [∀ p i, MeasurableSpace (R p i)] [∀ p i, BorelSpace (R p i)]
    [∀ p i, SecondCountableTopology (R p i)]
    [∀ p, MeasurableSpace (∀ i, R p i)ˣ] [∀ p, BorelSpace (∀ i, R p i)ˣ]
    (μ : ∀ p i, Measure (R p i)) [∀ p i, IsProbabilityMeasure (μ p i)]
    [∀ p i, (μ p i).IsAddHaarMeasure]
    (ν : ∀ p, Measure (∀ i, R p i)ˣ) [∀ p, IsProbabilityMeasure (ν p)]
    [∀ p, (ν p).IsMulRightInvariant]
    (L : ∀ p : S, Submodule (PadicInt p.val) (∀ i, R p i))
    [∀ p, Finite ((∀ i, R p i) ⧸ L p)]

include μ in
 

theorem global_local_weight_moment_of_support_prod_le_oai
    (hn : 0 < n) (ε : ℝ) (hε : 0 < ε)
    (hL : ∀ p, MeasurableSet (L p : Set (∀ i, R p i)))
    (hprod : (∏ p ∈ S, (p : ℝ)) ≤ (localIndexProduct S ι R L : ℝ))
    (hsat : ∀ p, Ideal.span (L p : Set (∀ i, R p i)) = ⊤)
    (e f : ∀ p, ι p → ℕ) (he0 : ∀ p i, 0 < e p i) (hf0 : ∀ p i, 0 < f p i)
    (he : ∀ p i, addVal (R p i) (algebraMap (PadicInt p.val) (R p i) p.val) = e p i)
    (hcard : ∀ p i, Nat.card (IsLocalRing.ResidueField (R p i)) = p.val ^ f p i)
    (hdegree : ∀ p, ∑ i, f p i * e p i = n) :
    (∑' k : ∀ p, ι p → ℕ, packetLocalWeight S ι R ν L k *
      packetLocalNorm S ι R k ^ (1 / (2 * (n : ℝ)) - 1)) ≤
      (localIndexProduct S ι R L : ℝ≥0∞)⁻¹ *
        ENNReal.ofReal (localProductConstant n ε hε * (localIndexProduct S ι R L : ℝ) ^ ε) := by
  have hnum (p : S) : Fintype.card (ι p) ≤ n := by
    rw [← hdegree p, ← Finset.card_univ]
    calc
      _ = ∑ _i : ι p, 1 := by simp
      _ ≤ _ := Finset.sum_le_sum (fun i _ => Nat.mul_pos (hf0 p i) (he0 p i))
  have hmajor := localProductConstant_bound n ε hε S (localIndexProduct S ι R L : ℝ)
    (fun p hp => (show Fact p.Prime from inferInstanceAs (Fact (⟨p, hp⟩ : S).val.Prime)).out.one_le)
    hprod
  have hfactor := local_weight_product_factorization (fun p : S => ι p → ℕ)
    (fun p k => localShellProbability (R p) (ν p) (L p) k)
    (fun p k => shellNorm (R p) k) (1 / (2 * (n : ℝ)) - 1)
  unfold packetLocalWeight packetLocalNorm
  have hid : (∑' k : ∀ p, ι p → ℕ,
      (∏ p, localShellProbability (R p) (ν p) (L p) (k p)) *
        (∏ p, shellNorm (R p) (k p)) ^ (1 / (2 * (n : ℝ)) - 1)) =
      ∏ p, ∑' k : ι p → ℕ, localShellProbability (R p) (ν p) (L p) k *
        shellNorm (R p) k ^ (1 / (2 * (n : ℝ)) - 1) := by
    simpa only [ENNReal.prod_rpow_of_ne_top (fun p _ => shellNorm_ne_top (R p) _) _] using hfactor
  rw [hid]
  calc
    _ ≤ ∏ p : S, ((L p).cardQuot : ℝ≥0∞)⁻¹ * ENNReal.ofReal (localMajorant n p.val) := by
      apply Finset.prod_le_prod'
      intro p _
      apply (local_weight_moment (R p) (μ p) (ν p) p.val (L p) (hL p) (hsat p)
        (e p) (f p) (he0 p) (hf0 p) (he p) (hcard p) n hn (hdegree p)).trans
      apply mul_le_mul_right
      exact localEulerFactor_le_majorant (R p) p.val n (Fact.out : p.val.Prime).one_lt
        (f p) (hf0 p) (hcard p) (hnum p)
    _ = (localIndexProduct S ι R L : ℝ≥0∞)⁻¹ *
        ENNReal.ofReal (∏ p ∈ S, localMajorant n p) := by
      rw [Finset.prod_mul_distrib]
      congr 1
      · rw [localIndexProduct, Nat.cast_prod]
        exact (ENNReal.prod_inv_distrib (fun _ _ _ _ _ => Or.inr (by simp))).symm
      · rw [← Finset.prod_coe_sort S]
        exact (ENNReal.ofReal_prod_of_nonneg (fun p _ =>
          localMajorant_nonneg n p.val (Fact.out : p.val.Prime).one_le)).symm
    _ ≤ _ := mul_le_mul_right (ENNReal.ofReal_le_ofReal hmajor) _

end



end PrimeDegreePackets


end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.PrimeDegreePackets.global_local_weight_moment_of_support_prod_le_oai.{u_1, u_2} := @OAI.PrimeDegreePackets.global_local_weight_moment_of_support_prod_le_oai.{u_1, u_2}
