-- Prove2me | solution 1 for IsDedekindDomain.HeightOneSpectrum.inertia_asIdeal_pow_succ_eq_map_subtype_lowerRamificationGroup
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/3a0f6f1c-1096-5710-afff-4adaa956839c

import Mathlib
import Definitions.Def_Mathlib_RingTheory_Valuation_LowerRamificationGroup
import Definitions.Def_NumberField_PlaceDecompositionAction
import Theorems.Thm_Ideal_inertia_pow_succ_eq_map_lowerRamificationGroup_of_dense
import Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_stabilizer_asIdeal_eq_decompositionSubgroup_valuationSubring
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsDedekindDomain_HeightOneSpectrum_inertia_asIdeal_pow_succ_eq_map_subtype_lowerRamificationGroup

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Pointwise

namespace DictBody

section P
variable {K : Type*} [Field K] (val : Valuation K (WithZero (Multiplicative ℤ)))

theorem le_exp_neg_one_of_lt_one {t : WithZero (Multiplicative ℤ)} (ht : t < 1) :
    t ≤ WithZero.exp (-1 : ℤ) := by
  rcases eq_or_ne t 0 with rfl | h0
  · exact zero_le'
  · obtain ⟨z, rfl⟩ : ∃ z : ℤ, t = WithZero.exp z := ⟨WithZero.log t, (WithZero.exp_log h0).symm⟩
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at ht
    rw [WithZero.exp_le_exp]
    omega

theorem integers_valuationSubring : val.Integers val.valuationSubring where
  hom_inj := Subtype.val_injective
  map_le_one x := x.2
  exists_of_le_one r hr := ⟨⟨r, hr⟩, rfl⟩

theorem mem_maximalIdeal_iff' (x : val.valuationSubring) :
    x ∈ IsLocalRing.maximalIdeal val.valuationSubring ↔ val (x : K) < 1 := by
  rw [ValuationSubring.valuation_lt_one_iff]
  exact ((Valuation.isEquiv_valuation_valuationSubring val).lt_one_iff_lt_one).symm

theorem mem_maximalIdeal_pow_iff_of_uniformizer {π : K} (hπ : val π = WithZero.exp (-1 : ℤ)) (n : ℕ)
    (x : val.valuationSubring) :
    x ∈ IsLocalRing.maximalIdeal val.valuationSubring ^ n ↔ val (x : K) ≤ WithZero.exp (-(n : ℤ)) := by
  have hπA : π ∈ val.valuationSubring := by
    rw [Valuation.mem_valuationSubring_iff, hπ, ← WithZero.exp_zero, WithZero.exp_le_exp]; omega
  set ϖ : val.valuationSubring := ⟨π, hπA⟩ with hϖ
  have hint := integers_valuationSubring val
  have hmax : IsLocalRing.maximalIdeal val.valuationSubring = Ideal.span {ϖ} := by
    apply le_antisymm
    · intro x hx
      rw [mem_maximalIdeal_iff'] at hx
      rw [Ideal.mem_span_singleton, ← hint.le_iff_dvd]
      change val (x : K) ≤ val π
      rw [hπ]
      exact le_exp_neg_one_of_lt_one hx
    · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, mem_maximalIdeal_iff']
      change val π < 1
      rw [hπ, ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
  rw [hmax, Ideal.span_singleton_pow, Ideal.mem_span_singleton, ← hint.le_iff_dvd]
  change val (x : K) ≤ val ((ϖ ^ n : val.valuationSubring) : K) ↔ _
  have : val ((ϖ ^ n : val.valuationSubring) : K) = WithZero.exp (-(n : ℤ)) := by
    rw [SubmonoidClass.coe_pow]
    change val (π ^ n) = _
    rw [map_pow, hπ, ← WithZero.exp_nsmul]
    congr 1
    simp
  rw [this]

end P

theorem mem_pow_valuationSubring_iff {F : Type*} [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F))
    (n : ℕ) (x : ↥((w.valuation F).valuationSubring)) :
    x ∈ IsLocalRing.maximalIdeal ↥((w.valuation F).valuationSubring) ^ n ↔
      w.valuation F (x : F) ≤ WithZero.exp (-(n : ℤ)) := by
  obtain ⟨π, hπ⟩ := w.valuation_exists_uniformizer F
  exact mem_maximalIdeal_pow_iff_of_uniformizer (w.valuation F) hπ n x

end DictBody

open DictBody in
theorem solution
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F]
    (w : HeightOneSpectrum (𝓞 F)) (i : ℕ) :
    (w.asIdeal ^ (i + 1)).inertia (F ≃ₐ[E] F) =
      (((w.valuation F).valuationSubring).lowerRamificationGroup E i).map
        (((w.valuation F).valuationSubring).decompositionSubgroup E).subtype := by
  classical

  have hmem : ∀ x : 𝓞 F, (algebraMap (𝓞 F) F x) ∈ (w.valuation F).valuationSubring := fun x =>
    (Valuation.mem_valuationSubring_iff _ _).2 (w.valuation_le_one x)
  let f : 𝓞 F →+* ↥((w.valuation F).valuationSubring) :=
    { toFun := fun x => ⟨algebraMap (𝓞 F) F x, hmem x⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun x y => Subtype.ext (map_mul _ x y)
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun x y => Subtype.ext (map_add _ x y) }
  have hfval : ∀ x : 𝓞 F, ((f x : ↥((w.valuation F).valuationSubring)) : F) = algebraMap (𝓞 F) F x := fun x => rfl

  have hj : ∀ σ : F ≃ₐ[E] F, (∀ x ∈ w.asIdeal, σ • x ∈ w.asIdeal) →
      σ ∈ (((w.valuation F).valuationSubring).decompositionSubgroup E).subtype.range := by
    intro σ hσ
    rw [Subgroup.range_subtype, ← IsDedekindDomain.HeightOneSpectrum.stabilizer_asIdeal_eq_decompositionSubgroup_valuationSubring E F w,
      MulAction.mem_stabilizer_iff]
    haveI := w.isMaximal
    have hle : σ • w.asIdeal ≤ w.asIdeal := by
      rw [Ideal.pointwise_smul_def, Ideal.map_le_iff_le_comap]
      intro x hx
      exact hσ x hx
    have hprime : (σ • w.asIdeal).IsPrime := w.isPrime.smul σ
    have hne : σ • w.asIdeal ≠ ⊥ := by
      intro h
      apply w.ne_bot
      have h2 : σ⁻¹ • (σ • w.asIdeal) = w.asIdeal := inv_smul_smul σ w.asIdeal
      rw [h] at h2
      rw [← h2, Ideal.pointwise_smul_def, Ideal.map_bot]
    have hmax : (σ • w.asIdeal).IsMaximal := hprime.isMaximal hne
    exact hmax.eq_of_le w.isMaximal.ne_top hle

  have hf : ∀ (γ : ↥(((w.valuation F).valuationSubring).decompositionSubgroup E)) (x : 𝓞 F),
      f ((((w.valuation F).valuationSubring).decompositionSubgroup E).subtype γ • x) = γ • f x :=
    fun γ x => Subtype.ext rfl

  have hcomap : ∀ n : ℕ, (IsLocalRing.maximalIdeal ↥((w.valuation F).valuationSubring) ^ n).comap f = w.asIdeal ^ n := by
    intro n
    ext x
    rw [Ideal.mem_comap, mem_pow_valuationSubring_iff, hfval, HeightOneSpectrum.valuation_of_algebraMap,
      HeightOneSpectrum.intValuation_le_pow_iff_mem]

  have hdense : ∀ (n : ℕ) (y : ↥((w.valuation F).valuationSubring)),
      ∃ x : 𝓞 F, y - f x ∈ IsLocalRing.maximalIdeal ↥((w.valuation F).valuationSubring) ^ n := by
    intro n y
    obtain ⟨a, ha⟩ := HeightOneSpectrum.exists_valuation_sub_lt_of_integer (R := 𝓞 F) (v := w)
      ((Valuation.mem_valuationSubring_iff _ _).1 y.2) (Units.mk0 (WithZero.exp (-(n : ℤ))) WithZero.coe_ne_zero)
    refine ⟨a, ?_⟩
    rw [mem_pow_valuationSubring_iff, AddSubgroupClass.coe_sub, hfval, Valuation.map_sub_swap]
    rw [Units.val_mk0] at ha
    exact ha.le
  have key := Ideal.inertia_pow_succ_eq_map_lowerRamificationGroup_of_dense (G := F ≃ₐ[E] F) w.asIdeal
    (((w.valuation F).valuationSubring).decompositionSubgroup E).subtype hj f hf hcomap hdense i
  exact key

end S_IsDedekindDomain_HeightOneSpectrum_inertia_asIdeal_pow_succ_eq_map_subtype_lowerRamificationGroup
end P2MW
export P2MW.S_IsDedekindDomain_HeightOneSpectrum_inertia_asIdeal_pow_succ_eq_map_subtype_lowerRamificationGroup (solution)
