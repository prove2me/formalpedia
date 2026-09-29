-- Prove2me | solution 1 for IsDiscreteValuationRing.exists_finset_card_le_forall_exists_sub_mul_finprod_smul_mem_pow_of_prime_card
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/14e6a563-259b-57c9-bfe0-563344437bd1

import Mathlib
import Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup
import Definitions.Def_Mathlib_RingTheory_Invariant_FixedSubringLocal
import Theorems.Thm_FixedPoints_isDiscreteValuationRing_subring
import Theorems.Thm_IsDiscreteValuationRing_addVal_coe_eq_lowerRamificationCard_zero_mul_addVal_fixedPoints
import Theorems.Thm_prod_one_add_smul_eq_one_add_finsum_add_finprod_add_finsum_smul_of_prime_card
import Theorems.Thm_IsDiscreteValuationRing_finsum_smul_mem_maximalIdeal_pow_of_lowerRamificationGroup_eq_top_of_eq_bot
import Theorems.Thm_IsDiscreteValuationRing_exists_sub_one_mem_and_finprod_smul_sub_mem_of_jump_lt_of_prime_card
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsDiscreteValuationRing_exists_finset_card_le_forall_exists_sub_mul_finprod_smul_mem_pow_of_prime_card

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxSynthPendingDepth 3

namespace IsDiscreteValuationRing
p2m_export "IsDiscreteValuationRing" "mk maximalIdeal addVal_eq_zero_of_unit addVal addVal_le_iff_dvd eq_unit_mul_pow_irreducible exists_irreducible addVal_pow addVal_uniformizer addVal_zero addVal_mul addVal_coe_eq_lowerRamificationCard_zero_mul_addVal_fixedPoints finsum_smul_mem_maximalIdeal_pow_of_lowerRamificationGroup_eq_top_of_eq_bot exists_sub_one_mem_and_finprod_smul_sub_mem_of_jump_lt_of_prime_card"
namespace TraceValSol
p2m_open "IsDiscreteValuationRing~addVal_smul~mem_maximalIdeal_pow_iff_le_addVal"

section dvr
variable {B : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]

theorem mem_maximalIdeal_pow_iff_le_addVal (y : B) (n : ℕ) :
    y ∈ IsLocalRing.maximalIdeal B ^ n ↔ (n : ℕ∞) ≤ IsDiscreteValuationRing.addVal B y := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible B
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    ← IsDiscreteValuationRing.addVal_le_iff_dvd, IsDiscreteValuationRing.addVal_pow,
    IsDiscreteValuationRing.addVal_uniformizer hϖ, nsmul_one]

theorem span_singleton_eq_maximalIdeal_pow_of_addVal_eq {y : B} {n : ℕ}
    (h : IsDiscreteValuationRing.addVal B y = n) : Ideal.span {y} = IsLocalRing.maximalIdeal B ^ n := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible B
  have hy0 : y ≠ 0 := by
    intro h0
    rw [h0, IsDiscreteValuationRing.addVal_zero] at h
    exact ENat.top_ne_coe _ h
  obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy0 hϖ
  have hk : k = n := by
    rw [IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_pow,
      IsDiscreteValuationRing.addVal_uniformizer hϖ, nsmul_one,
      IsDiscreteValuationRing.addVal_eq_zero_of_unit, zero_add] at h
    exact_mod_cast h
  subst hk
  rw [Ideal.span_singleton_mul_left_unit u.isUnit, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]

end dvr

end IsDiscreteValuationRing.TraceValSol

section GRINJ

namespace IsDiscreteValuationRing
p2m_export "IsDiscreteValuationRing" "mk maximalIdeal addVal_eq_zero_of_unit addVal addVal_le_iff_dvd eq_unit_mul_pow_irreducible exists_irreducible addVal_pow addVal_uniformizer addVal_zero addVal_mul addVal_coe_eq_lowerRamificationCard_zero_mul_addVal_fixedPoints finsum_smul_mem_maximalIdeal_pow_of_lowerRamificationGroup_eq_top_of_eq_bot exists_sub_one_mem_and_finprod_smul_sub_mem_of_jump_lt_of_prime_card"
namespace XCNormGrInj
p2m_open "IsDiscreteValuationRing~addVal_smul~mem_maximalIdeal_pow_iff_le_addVal"

variable {B : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable {G : Type*} [Group G] [MulSemiringAction G B]

theorem smul_mem_maximalIdeal_pow_iff (σ : G) (x : B) (k : ℕ) :
    σ • x ∈ IsLocalRing.maximalIdeal B ^ k ↔ x ∈ IsLocalRing.maximalIdeal B ^ k := by
  constructor
  · intro h
    have h' := (Ideal.smul_mem_pointwise_smul_iff (a := σ⁻¹)).mpr h
    rwa [IsLocalRing.pointwise_smul_maximalIdeal_pow, inv_smul_smul] at h'
  · intro h
    have h' := (Ideal.smul_mem_pointwise_smul_iff (a := σ)).mpr h
    rwa [IsLocalRing.pointwise_smul_maximalIdeal_pow] at h'

theorem addVal_smul (σ : G) (x : B) : addVal B (σ • x) = addVal B x := by
  have key : ∀ k : ℕ, (k : ℕ∞) ≤ addVal B (σ • x) ↔ (k : ℕ∞) ≤ addVal B x := fun k => by
    rw [← IsDiscreteValuationRing.TraceValSol.mem_maximalIdeal_pow_iff_le_addVal,
      ← IsDiscreteValuationRing.TraceValSol.mem_maximalIdeal_pow_iff_le_addVal, smul_mem_maximalIdeal_pow_iff]
  exact le_antisymm (ENat.forall_natCast_le_iff_le.mp fun k hk => (key k).mp hk)
    (ENat.forall_natCast_le_iff_le.mp fun k hk => (key k).mpr hk)

theorem addVal_prod {ι : Type*} (s : Finset ι) (f : ι → B) :
    addVal B (∏ i ∈ s, f i) = ∑ i ∈ s, addVal B (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.sum_empty, AddValuation.map_one]
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, IsDiscreteValuationRing.addVal_mul, ih]

theorem mem_maximalIdeal_pow_of_finprod_smul_mem [Finite G] (x : B) (k : ℕ)
    (h : ∏ᶠ σ : G, σ • x ∈ IsLocalRing.maximalIdeal B ^ (Nat.card G * k)) : x ∈ IsLocalRing.maximalIdeal B ^ k := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  have hcard : 0 < Nat.card G := Nat.card_pos
  rw [IsDiscreteValuationRing.TraceValSol.mem_maximalIdeal_pow_iff_le_addVal] at h ⊢
  rw [finprod_eq_prod_of_fintype, addVal_prod, Finset.sum_congr rfl (fun σ _ => addVal_smul σ x), Finset.sum_const,
    Finset.card_univ, ← Nat.card_eq_fintype_card] at h
  by_cases htop : addVal B x = ⊤
  · rw [htop]; exact le_top
  · obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.mp htop
    rw [← ha] at h ⊢
    rw [nsmul_eq_mul, ← Nat.cast_mul, Nat.cast_le] at h
    exact Nat.cast_le.mpr (Nat.le_of_mul_le_mul_left h hcard)

theorem succ_le_div_of_lt {ℓ t m : ℕ} (hℓ : 2 ≤ ℓ) (hm : m < t) :
    m + 1 ≤ (m + (t + 1) * (ℓ - 1)) / ℓ := by
  obtain ⟨k, rfl⟩ : ∃ k, ℓ = k + 1 := ⟨ℓ - 1, by omega⟩
  have hk : 1 ≤ k := by omega
  simp only [Nat.add_sub_cancel]
  refine (Nat.le_div_iff_mul_le (by omega)).mpr ?_
  have : (m + 1) * k ≤ t * k := Nat.mul_le_mul_right k hm
  nlinarith

end IsDiscreteValuationRing.XCNormGrInj

namespace IsDiscreteValuationRing p2m_export "IsDiscreteValuationRing" "mk maximalIdeal addVal_eq_zero_of_unit addVal addVal_le_iff_dvd eq_unit_mul_pow_irreducible exists_irreducible addVal_pow addVal_uniformizer addVal_zero addVal_mul addVal_coe_eq_lowerRamificationCard_zero_mul_addVal_fixedPoints finsum_smul_mem_maximalIdeal_pow_of_lowerRamificationGroup_eq_top_of_eq_bot exists_sub_one_mem_and_finprod_smul_sub_mem_of_jump_lt_of_prime_card" end IsDiscreteValuationRing
p2m_open_scoped "IsDiscreteValuationRing" in
open IsDiscreteValuationRing.XCNormGrInj in

theorem IsDiscreteValuationRing.sub_one_mem_maximalIdeal_pow_succ_of_finprod_smul_sub_one_mem_of_lt_of_prime_card
    {B : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G B] [FaithfulSMul G B]
    [(IsLocalRing.maximalIdeal B).LiesOver (IsLocalRing.maximalIdeal (FixedPoints.subring B G))]
    [Algebra.IsSeparable
      (FixedPoints.subring B G ⧸ IsLocalRing.maximalIdeal (FixedPoints.subring B G))
      (B ⧸ IsLocalRing.maximalIdeal B)]
    (hℓ : (Nat.card G).Prime) (t : ℕ)
    (ht : IsLocalRing.lowerRamificationGroup B G t = ⊤) (ht' : IsLocalRing.lowerRamificationGroup B G (t + 1) = ⊥)
    (m : ℕ) (hm : m < t) (b : B)
    (hb : b - 1 ∈ IsLocalRing.maximalIdeal B ^ m)
    (hN : (∏ᶠ σ : G, σ • b) - 1 ∈ IsLocalRing.maximalIdeal B ^ (Nat.card G * (m + 1))) :
    b - 1 ∈ IsLocalRing.maximalIdeal B ^ (m + 1) := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  have hℓ2 : 2 ≤ Nat.card G := hℓ.two_le
  set γ := b - 1 with hγdef
  obtain ⟨δ, hδ, hexp⟩ := prod_one_add_smul_eq_one_add_finsum_add_finprod_add_finsum_smul_of_prime_card hℓ γ
  have hb1 : (∏ᶠ σ : G, σ • b) = ∏ᶠ σ : G, (1 + σ • γ) :=
    finprod_congr fun σ => by rw [show b = 1 + γ by rw [hγdef]; ring, smul_add, smul_one]
  rw [hb1, hexp, show (1 : B) + ∑ᶠ σ : G, σ • γ + ∏ᶠ σ : G, σ • γ + ∑ᶠ σ : G, σ • δ - 1 =
      ∑ᶠ σ : G, σ • γ + ∏ᶠ σ : G, σ • γ + ∑ᶠ σ : G, σ • δ by ring] at hN

  have hσγ : ∀ σ : G, σ • γ ∈ IsLocalRing.maximalIdeal B ^ m := fun σ => (smul_mem_maximalIdeal_pow_iff σ γ m).mpr hb
  have hδm : δ ∈ IsLocalRing.maximalIdeal B ^ (2 * m) := by
    refine (Ideal.span_le.mpr ?_) hδ
    rintro x ⟨σ₁, σ₂, -, rfl⟩
    rw [two_mul, pow_add]
    exact Ideal.mul_mem_mul (hσγ σ₁) (hσγ σ₂)

  have hk1 : m + 1 ≤ (m + (t + 1) * (Nat.card G - 1)) / Nat.card G := succ_le_div_of_lt hℓ2 hm
  have hTrγ : ∑ᶠ σ : G, σ • γ ∈ IsLocalRing.maximalIdeal B ^ (Nat.card G * (m + 1)) :=
    Ideal.pow_le_pow_right (Nat.mul_le_mul_left _ hk1)
      (IsDiscreteValuationRing.finsum_smul_mem_maximalIdeal_pow_of_lowerRamificationGroup_eq_top_of_eq_bot t ht ht' m γ hb)
  have hTrδ : ∑ᶠ σ : G, σ • δ ∈ IsLocalRing.maximalIdeal B ^ (Nat.card G * (m + 1)) := by
    refine Ideal.pow_le_pow_right (Nat.mul_le_mul_left _ (hk1.trans ?_))
      (IsDiscreteValuationRing.finsum_smul_mem_maximalIdeal_pow_of_lowerRamificationGroup_eq_top_of_eq_bot t ht ht' (2 * m) δ hδm)
    exact Nat.div_le_div_right (by omega)

  have hNγ : ∏ᶠ σ : G, σ • γ ∈ IsLocalRing.maximalIdeal B ^ (Nat.card G * (m + 1)) := by
    have h := Submodule.sub_mem _ (Submodule.sub_mem _ hN hTrγ) hTrδ
    rwa [show ∑ᶠ σ : G, σ • γ + ∏ᶠ σ : G, σ • γ + ∑ᶠ σ : G, σ • δ - ∑ᶠ σ : G, σ • γ - ∑ᶠ σ : G, σ • δ =
      ∏ᶠ σ : G, σ • γ by ring] at h

  exact mem_maximalIdeal_pow_of_finprod_smul_mem γ (m + 1) hNγ

end GRINJ

namespace IsDiscreteValuationRing
p2m_export "IsDiscreteValuationRing" "mk maximalIdeal addVal_eq_zero_of_unit addVal addVal_le_iff_dvd eq_unit_mul_pow_irreducible exists_irreducible addVal_pow addVal_uniformizer addVal_zero addVal_mul addVal_coe_eq_lowerRamificationCard_zero_mul_addVal_fixedPoints finsum_smul_mem_maximalIdeal_pow_of_lowerRamificationGroup_eq_top_of_eq_bot exists_sub_one_mem_and_finprod_smul_sub_mem_of_jump_lt_of_prime_card"
namespace XCGrCoker
p2m_open "IsDiscreteValuationRing~addVal_smul~mem_maximalIdeal_pow_iff_le_addVal"

p2m_open "IsLocalRing~smul_mem_maximalIdeal_pow_iff P2MW.S_IsDiscreteValuationRing_exists_finset_card_le_forall_exists_sub_mul_finprod_smul_mem_pow_of_prime_card.IsDiscreteValuationRing.XCNormGrInj"

section frame
variable {B : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable {G : Type*} [Group G] [Finite G] [MulSemiringAction G B]

theorem smul_finprod_smul (τ : G) (b : B) : τ • ∏ᶠ σ : G, σ • b = ∏ᶠ σ : G, σ • b := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  rw [finprod_eq_prod_of_fintype]
  exact Finset.smul_prod_perm b τ

theorem smul_finsum_smul (τ : G) (b : B) : τ • ∑ᶠ σ : G, σ • b = ∑ᶠ σ : G, σ • b := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  rw [finsum_eq_sum_of_fintype, Finset.smul_sum]
  exact Fintype.sum_equiv (MulAction.toPerm τ⁻¹)⁻¹ _ _ fun σ => by simp [mul_smul]

theorem finprod_smul_of_forall_smul_eq {a : B} (ha : ∀ σ : G, σ • a = a) : ∏ᶠ σ : G, σ • a = a ^ Nat.card G := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  rw [finprod_eq_prod_of_fintype, Finset.prod_congr rfl fun σ _ => ha σ, Finset.prod_const, Finset.card_univ,
    Nat.card_eq_fintype_card]

theorem finprod_smul_mul (a b : B) : ∏ᶠ σ : G, σ • (a * b) = (∏ᶠ σ : G, σ • a) * ∏ᶠ σ : G, σ • b := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  simp only [finprod_eq_prod_of_fintype, smul_mul', Finset.prod_mul_distrib]

theorem finsum_smul_mul_of_forall_smul_eq {a : B} (ha : ∀ σ : G, σ • a = a) (x : B) :
    ∑ᶠ σ : G, σ • (a * x) = a * ∑ᶠ σ : G, σ • x := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  simp only [finsum_eq_sum_of_fintype, smul_mul', ha, Finset.mul_sum]

theorem addVal_finprod_smul (b : B) : addVal B (∏ᶠ σ : G, σ • b) = Nat.card G • addVal B b := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  rw [finprod_eq_prod_of_fintype, addVal_prod, Finset.sum_congr rfl (fun σ _ => addVal_smul σ b), Finset.sum_const,
    Finset.card_univ, Nat.card_eq_fintype_card]

end frame

section fixedring
variable {B : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable {G : Type*} [Group G] [Finite G] [MulSemiringAction G B] [FaithfulSMul G B]
variable [(IsLocalRing.maximalIdeal B).LiesOver (IsLocalRing.maximalIdeal (FixedPoints.subring B G))]
variable [Algebra.IsSeparable
      (FixedPoints.subring B G ⧸ IsLocalRing.maximalIdeal (FixedPoints.subring B G))
      (B ⧸ IsLocalRing.maximalIdeal B)]

theorem mem_maximalIdeal_fixedPoints_pow_iff (h0 : IsLocalRing.lowerRamificationGroup B G 0 = ⊤)
    (x : FixedPoints.subring B G) (y : ℕ) :
    x ∈ IsLocalRing.maximalIdeal (FixedPoints.subring B G) ^ y ↔
      (x : B) ∈ IsLocalRing.maximalIdeal B ^ (Nat.card G * y) := by
  haveI : IsDiscreteValuationRing (FixedPoints.subring B G) := FixedPoints.isDiscreteValuationRing_subring
  have hcard0 : IsLocalRing.lowerRamificationCard B G 0 = Nat.card G := by
    rw [IsLocalRing.lowerRamificationCard, h0, Subgroup.card_top]
  have hcard : 0 < Nat.card G := Nat.card_pos
  rw [IsDiscreteValuationRing.TraceValSol.mem_maximalIdeal_pow_iff_le_addVal,
    IsDiscreteValuationRing.TraceValSol.mem_maximalIdeal_pow_iff_le_addVal,
    IsDiscreteValuationRing.addVal_coe_eq_lowerRamificationCard_zero_mul_addVal_fixedPoints x, hcard0]
  by_cases htop : addVal (FixedPoints.subring B G) x = ⊤
  · rw [htop, ENat.mul_top (Nat.cast_ne_zero.mpr hcard.ne')]
    exact ⟨fun _ => le_top, fun _ => le_top⟩
  · obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.mp htop
    rw [← ha, ← Nat.cast_mul, Nat.cast_le, Nat.cast_le]
    exact ⟨fun h => Nat.mul_le_mul_left _ h, fun h => Nat.le_of_mul_le_mul_left h hcard⟩

end fixedring

section below
variable {B : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable {G : Type*} [Group G] [Finite G] [MulSemiringAction G B] [FaithfulSMul G B]
variable [(IsLocalRing.maximalIdeal B).LiesOver (IsLocalRing.maximalIdeal (FixedPoints.subring B G))]
variable [Algebra.IsSeparable
      (FixedPoints.subring B G ⧸ IsLocalRing.maximalIdeal (FixedPoints.subring B G))
      (B ⧸ IsLocalRing.maximalIdeal B)]

theorem lowerRamificationGroup_zero_eq_top {t : ℕ} (ht : IsLocalRing.lowerRamificationGroup B G t = ⊤) :
    IsLocalRing.lowerRamificationGroup B G 0 = ⊤ :=
  top_le_iff.mp (ht ▸ IsLocalRing.lowerRamificationGroup_antitone (Nat.zero_le t))

theorem mem_maximalIdeal_pow_card_of_forall_smul_eq {t : ℕ} (ht : IsLocalRing.lowerRamificationGroup B G t = ⊤)
    {x : B} (hxG : ∀ σ : G, σ • x = x) (hx : x ∈ IsLocalRing.maximalIdeal B) :
    x ∈ IsLocalRing.maximalIdeal B ^ Nat.card G := by
  have hxA : x ∈ FixedPoints.subring B G := hxG
  have h := (mem_maximalIdeal_fixedPoints_pow_iff (lowerRamificationGroup_zero_eq_top ht) ⟨x, hxA⟩ 1).mp
  rw [pow_one, mul_one] at h
  apply h
  rw [FixedPoints.mem_maximalIdeal_subring_iff]
  exact hx

theorem mem_maximalIdeal_pow_card_mul_succ_of_forall_smul_eq {t : ℕ} (ht : IsLocalRing.lowerRamificationGroup B G t = ⊤)
    {x : B} (hxG : ∀ σ : G, σ • x = x) (y : ℕ) (hx : x ∈ IsLocalRing.maximalIdeal B ^ (Nat.card G * y + 1)) :
    x ∈ IsLocalRing.maximalIdeal B ^ (Nat.card G * (y + 1)) := by
  haveI : IsDiscreteValuationRing (FixedPoints.subring B G) := FixedPoints.isDiscreteValuationRing_subring
  have hxA : x ∈ FixedPoints.subring B G := hxG
  have h0 := lowerRamificationGroup_zero_eq_top ht

  have hcard : 0 < Nat.card G := Nat.card_pos
  have hcard0 : IsLocalRing.lowerRamificationCard B G 0 = Nat.card G := by
    rw [IsLocalRing.lowerRamificationCard, h0, Subgroup.card_top]
  rw [IsDiscreteValuationRing.TraceValSol.mem_maximalIdeal_pow_iff_le_addVal] at hx ⊢
  rw [show x = ((⟨x, hxA⟩ : FixedPoints.subring B G) : B) from rfl,
    IsDiscreteValuationRing.addVal_coe_eq_lowerRamificationCard_zero_mul_addVal_fixedPoints, hcard0] at hx ⊢
  by_cases htop : addVal (FixedPoints.subring B G) ⟨x, hxA⟩ = ⊤
  · rw [htop, ENat.mul_top (Nat.cast_ne_zero.mpr hcard.ne')]; exact le_top
  · obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.mp htop
    rw [← ha, ← Nat.cast_mul, Nat.cast_le] at hx ⊢
    have : y < a := by
      by_contra hle
      push Not at hle
      have := Nat.mul_le_mul_left (Nat.card G) hle
      omega
    exact Nat.mul_le_mul_left _ this

theorem natCast_card_mem_maximalIdeal (hℓ : (Nat.card G).Prime) {t : ℕ} (ht1 : 1 ≤ t)
    (ht : IsLocalRing.lowerRamificationGroup B G t = ⊤) :
    (Nat.card G : B) ∈ IsLocalRing.maximalIdeal B := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible B
  have hπm : π ∈ IsLocalRing.maximalIdeal B := hπ.not_isUnit
  have hG1 : IsLocalRing.lowerRamificationGroup B G 1 = ⊤ :=
    top_le_iff.mp (ht ▸ IsLocalRing.lowerRamificationGroup_antitone ht1)

  have h1 : ∑ σ : G, σ • π - (Nat.card G : B) * π ∈ IsLocalRing.maximalIdeal B ^ 2 := by
    have : ∑ σ : G, σ • π - (Nat.card G : B) * π = ∑ σ : G, (σ • π - π) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, nsmul_eq_mul]
    rw [this]
    refine Ideal.sum_mem _ fun σ _ => ?_
    have hσ : σ ∈ IsLocalRing.lowerRamificationGroup B G 1 := hG1 ▸ Subgroup.mem_top σ
    exact (IsLocalRing.mem_lowerRamificationGroup.mp hσ) π

  have h2 : ∑ σ : G, σ • π ∈ IsLocalRing.maximalIdeal B ^ 2 := by
    have hfix : ∀ τ : G, τ • ∑ σ : G, σ • π = ∑ σ : G, σ • π := fun τ => by
      have := smul_finsum_smul τ π (G := G); rwa [finsum_eq_sum_of_fintype] at this
    have hmem : ∑ σ : G, σ • π ∈ IsLocalRing.maximalIdeal B :=
      Ideal.sum_mem _ fun σ _ => (smul_mem_maximalIdeal_pow_iff σ π 1 |>.mpr (by rwa [pow_one])) |> fun h => by rwa [pow_one] at h
    exact Ideal.pow_le_pow_right hℓ.two_le (mem_maximalIdeal_pow_card_of_forall_smul_eq ht hfix hmem)
  have h3 : (Nat.card G : B) * π ∈ IsLocalRing.maximalIdeal B ^ 2 := by
    have := Submodule.sub_mem _ h2 h1; rwa [sub_sub_cancel] at this
  by_contra hℓm
  have hu : IsUnit (Nat.card G : B) := (IsLocalRing.notMem_maximalIdeal.mp hℓm)
  have hπ2 : π ∈ IsLocalRing.maximalIdeal B ^ 2 := by
    obtain ⟨u, hu⟩ := hu
    rw [← hu] at h3
    exact (Ideal.unit_mul_mem_iff_mem _ u.isUnit).mp h3

  rw [IsDiscreteValuationRing.TraceValSol.mem_maximalIdeal_pow_iff_le_addVal, IsDiscreteValuationRing.addVal_uniformizer hπ] at hπ2
  exact absurd hπ2 (by decide)

end below

section core
variable {B : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable {G : Type*} [Group G] [Finite G] [MulSemiringAction G B] [FaithfulSMul G B]
variable [(IsLocalRing.maximalIdeal B).LiesOver (IsLocalRing.maximalIdeal (FixedPoints.subring B G))]
variable [Algebra.IsSeparable
      (FixedPoints.subring B G ⧸ IsLocalRing.maximalIdeal (FixedPoints.subring B G))
      (B ⧸ IsLocalRing.maximalIdeal B)]

theorem finprod_one_add_smul_sub_one_sub_finprod_mem (hℓ : (Nat.card G).Prime) (t : ℕ)
    (ht : IsLocalRing.lowerRamificationGroup B G t = ⊤) (ht' : IsLocalRing.lowerRamificationGroup B G (t + 1) = ⊥)
    (m : ℕ) (hm : m < t) (γ : B) (hγ : γ ∈ IsLocalRing.maximalIdeal B ^ m) :
    (∏ᶠ σ : G, (1 + σ • γ)) - 1 - ∏ᶠ σ : G, σ • γ ∈ IsLocalRing.maximalIdeal B ^ (Nat.card G * (m + 1)) := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  have hℓ2 : 2 ≤ Nat.card G := hℓ.two_le
  obtain ⟨δ, hδ, hexp⟩ := prod_one_add_smul_eq_one_add_finsum_add_finprod_add_finsum_smul_of_prime_card hℓ γ
  rw [hexp, show (1 : B) + ∑ᶠ σ : G, σ • γ + ∏ᶠ σ : G, σ • γ + ∑ᶠ σ : G, σ • δ - 1 - ∏ᶠ σ : G, σ • γ =
      ∑ᶠ σ : G, σ • γ + ∑ᶠ σ : G, σ • δ by ring]
  have hσγ : ∀ σ : G, σ • γ ∈ IsLocalRing.maximalIdeal B ^ m := fun σ => (smul_mem_maximalIdeal_pow_iff σ γ m).mpr hγ
  have hδm : δ ∈ IsLocalRing.maximalIdeal B ^ (2 * m) := by
    refine (Ideal.span_le.mpr ?_) hδ
    rintro x ⟨σ₁, σ₂, -, rfl⟩
    rw [two_mul, pow_add]
    exact Ideal.mul_mem_mul (hσγ σ₁) (hσγ σ₂)
  have hk1 : m + 1 ≤ (m + (t + 1) * (Nat.card G - 1)) / Nat.card G := succ_le_div_of_lt hℓ2 hm
  refine Submodule.add_mem _ ?_ ?_
  · exact Ideal.pow_le_pow_right (Nat.mul_le_mul_left _ hk1)
      (IsDiscreteValuationRing.finsum_smul_mem_maximalIdeal_pow_of_lowerRamificationGroup_eq_top_of_eq_bot t ht ht' m γ hγ)
  · refine Ideal.pow_le_pow_right (Nat.mul_le_mul_left _ (hk1.trans ?_))
      (IsDiscreteValuationRing.finsum_smul_mem_maximalIdeal_pow_of_lowerRamificationGroup_eq_top_of_eq_bot t ht ht' (2 * m) δ hδm)
    exact Nat.div_le_div_right (by omega)

theorem jump_arith {ℓ t : ℕ} (hℓ : 2 ≤ ℓ) (ht1 : 1 ≤ t) :
    t + 1 ≤ (2 * t + (t + 1) * (ℓ - 1)) / ℓ ∧ t ≤ (t + (t + 1) * (ℓ - 1)) / ℓ := by
  obtain ⟨k, rfl⟩ : ∃ k, ℓ = k + 1 := ⟨ℓ - 1, by omega⟩
  have hk : 1 ≤ k := by omega
  simp only [Nat.add_sub_cancel]
  constructor
  · refine (Nat.le_div_iff_mul_le (by omega)).mpr ?_
    nlinarith
  · refine (Nat.le_div_iff_mul_le (by omega)).mpr ?_
    nlinarith

theorem finprod_one_add_smul_sub_one_sub_finsum_sub_finprod_mem (hℓ : (Nat.card G).Prime) (t : ℕ) (ht1 : 1 ≤ t)
    (ht : IsLocalRing.lowerRamificationGroup B G t = ⊤) (ht' : IsLocalRing.lowerRamificationGroup B G (t + 1) = ⊥)
    (γ : B) (hγ : γ ∈ IsLocalRing.maximalIdeal B ^ t) :
    (∏ᶠ σ : G, (1 + σ • γ)) - 1 - ∑ᶠ σ : G, σ • γ - ∏ᶠ σ : G, σ • γ ∈
      IsLocalRing.maximalIdeal B ^ (Nat.card G * (t + 1)) := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  have hℓ2 : 2 ≤ Nat.card G := hℓ.two_le
  obtain ⟨δ, hδ, hexp⟩ := prod_one_add_smul_eq_one_add_finsum_add_finprod_add_finsum_smul_of_prime_card hℓ γ
  rw [hexp, show (1 : B) + ∑ᶠ σ : G, σ • γ + ∏ᶠ σ : G, σ • γ + ∑ᶠ σ : G, σ • δ - 1 - ∑ᶠ σ : G, σ • γ - ∏ᶠ σ : G, σ • γ =
      ∑ᶠ σ : G, σ • δ by ring]
  have hσγ : ∀ σ : G, σ • γ ∈ IsLocalRing.maximalIdeal B ^ t := fun σ => (smul_mem_maximalIdeal_pow_iff σ γ t).mpr hγ
  have hδm : δ ∈ IsLocalRing.maximalIdeal B ^ (2 * t) := by
    refine (Ideal.span_le.mpr ?_) hδ
    rintro x ⟨σ₁, σ₂, -, rfl⟩
    rw [two_mul, pow_add]
    exact Ideal.mul_mem_mul (hσγ σ₁) (hσγ σ₂)
  refine Ideal.pow_le_pow_right (Nat.mul_le_mul_left _ (jump_arith hℓ2 ht1).1)
    (IsDiscreteValuationRing.finsum_smul_mem_maximalIdeal_pow_of_lowerRamificationGroup_eq_top_of_eq_bot t ht ht' (2 * t) δ hδm)

theorem finsum_smul_mem_of_mem_pow_jump (hℓ : (Nat.card G).Prime) (t : ℕ) (ht1 : 1 ≤ t)
    (ht : IsLocalRing.lowerRamificationGroup B G t = ⊤) (ht' : IsLocalRing.lowerRamificationGroup B G (t + 1) = ⊥)
    (γ : B) (hγ : γ ∈ IsLocalRing.maximalIdeal B ^ t) :
    ∑ᶠ σ : G, σ • γ ∈ IsLocalRing.maximalIdeal B ^ (Nat.card G * t) :=
  Ideal.pow_le_pow_right (Nat.mul_le_mul_left _ (jump_arith hℓ.two_le ht1).2)
    (IsDiscreteValuationRing.finsum_smul_mem_maximalIdeal_pow_of_lowerRamificationGroup_eq_top_of_eq_bot t ht ht' t γ hγ)

theorem isUnit_one_add_of_mem {x : B} (hx : x ∈ IsLocalRing.maximalIdeal B) : IsUnit (1 + x) := by
  by_contra h
  have h1 : (1 : B) + x ∈ IsLocalRing.maximalIdeal B := (IsLocalRing.mem_maximalIdeal _).mpr h
  have : (1 : B) ∈ IsLocalRing.maximalIdeal B := by
    have := Submodule.sub_mem _ h1 hx; rwa [add_sub_cancel_right] at this
  exact (IsLocalRing.maximalIdeal.isMaximal B).ne_top (Ideal.eq_top_of_isUnit_mem _ this isUnit_one)

theorem pow_surjective_of_natCast_eq_zero {k : Type*} [Field k] [Finite k] {ℓ : ℕ} (hℓ : ℓ.Prime)
    (h0 : (ℓ : k) = 0) : Function.Surjective fun x : k => x ^ ℓ := by
  haveI := Fact.mk hℓ
  haveI : CharP k ℓ := ringChar.eq_iff.mp (CharP.ringChar_of_prime_eq_zero hℓ h0)
  apply Finite.injective_iff_surjective.mp
  intro x y hxy
  have hxy' : x ^ ℓ = y ^ ℓ := hxy
  have : (x - y) ^ ℓ = 0 := by rw [sub_pow_char, hxy', sub_self]
  exact sub_eq_zero.mp (pow_eq_zero_iff hℓ.ne_zero |>.mp this)

end core

section belowmain
variable {B : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable {G : Type*} [Group G] [Finite G] [MulSemiringAction G B] [FaithfulSMul G B]
variable [(IsLocalRing.maximalIdeal B).LiesOver (IsLocalRing.maximalIdeal (FixedPoints.subring B G))]
variable [Algebra.IsSeparable
      (FixedPoints.subring B G ⧸ IsLocalRing.maximalIdeal (FixedPoints.subring B G))
      (B ⧸ IsLocalRing.maximalIdeal B)]

theorem exists_uniformizer_package {t : ℕ} (ht : IsLocalRing.lowerRamificationGroup B G t = ⊤) :
    ∃ π ϖ : B, Irreducible π ∧ (∀ σ : G, σ • ϖ = ϖ) ∧ ϖ = ∏ᶠ σ : G, σ • π ∧ ϖ ∈ IsLocalRing.maximalIdeal B ^ Nat.card G ∧
      ∀ (y : ℕ) (α : B), (∀ σ : G, σ • α = α) → α ∈ IsLocalRing.maximalIdeal B ^ (Nat.card G * y) →
        ∃ β : B, (∀ σ : G, σ • β = β) ∧ α = ϖ ^ y * β := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  let A := FixedPoints.subring B G
  haveI : IsDiscreteValuationRing A := FixedPoints.isDiscreteValuationRing_subring
  have h0 := lowerRamificationGroup_zero_eq_top ht
  have hcard : 0 < Nat.card G := Nat.card_pos
  have hcard0 : IsLocalRing.lowerRamificationCard B G 0 = Nat.card G := by
    rw [IsLocalRing.lowerRamificationCard, h0, Subgroup.card_top]
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible B
  have hϖG : ∀ τ : G, τ • ∏ᶠ σ : G, σ • π = ∏ᶠ σ : G, σ • π := fun τ => smul_finprod_smul τ π
  let ϖA : A := ⟨∏ᶠ σ : G, σ • π, hϖG⟩
  have hvϖB : addVal B (∏ᶠ σ : G, σ • π) = (Nat.card G : ℕ∞) := by
    rw [addVal_finprod_smul, IsDiscreteValuationRing.addVal_uniformizer hπ, nsmul_one]
  have hvϖA : addVal A ϖA = 1 := by
    have h := IsDiscreteValuationRing.addVal_coe_eq_lowerRamificationCard_zero_mul_addVal_fixedPoints ϖA
    rw [hcard0] at h
    change addVal B (∏ᶠ σ : G, σ • π) = _ at h
    rw [hvϖB] at h
    by_cases htop : addVal A ϖA = ⊤
    · rw [htop, ENat.mul_top (Nat.cast_ne_zero.mpr hcard.ne')] at h
      exact absurd h (ENat.coe_ne_top _)
    · obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.mp htop
      rw [← ha, ← Nat.cast_mul, Nat.cast_inj] at h
      rw [← ha]
      have : a = 1 := by
        have h' : Nat.card G * 1 = Nat.card G * a := by rw [mul_one]; exact h
        exact (Nat.eq_of_mul_eq_mul_left hcard h').symm
      rw [this]; rfl
  refine ⟨π, ∏ᶠ σ : G, σ • π, hπ, hϖG, rfl, ?_, ?_⟩
  · rw [IsDiscreteValuationRing.TraceValSol.mem_maximalIdeal_pow_iff_le_addVal, hvϖB]
  · intro y α hαG hα
    let αA : A := ⟨α, hαG⟩
    have hαA : αA ∈ IsLocalRing.maximalIdeal A ^ y := (mem_maximalIdeal_fixedPoints_pow_iff h0 αA y).mpr hα
    have hdvd : ϖA ^ y ∣ αA := by
      rw [← IsDiscreteValuationRing.addVal_le_iff_dvd, IsDiscreteValuationRing.addVal_pow, hvϖA, nsmul_one]
      exact (IsDiscreteValuationRing.TraceValSol.mem_maximalIdeal_pow_iff_le_addVal αA y).mp hαA
    obtain ⟨βA, hβ⟩ := hdvd
    refine ⟨(βA : B), βA.2, ?_⟩
    have := congrArg (fun z : A => (z : B)) hβ
    simpa using this

theorem exists_finprod_smul_sub_mem_of_lt_jump (hℓ : (Nat.card G).Prime) (t : ℕ)
    (ht : IsLocalRing.lowerRamificationGroup B G t = ⊤) (ht' : IsLocalRing.lowerRamificationGroup B G (t + 1) = ⊥)
    [Finite (B ⧸ IsLocalRing.maximalIdeal B)]
    (y : ℕ) (hy : y < t) (a : B) (hau : IsUnit a) (haG : ∀ σ : G, σ • a = a)
    (ha : a - 1 ∈ IsLocalRing.maximalIdeal B ^ (Nat.card G * y)) :
    ∃ b : B, IsUnit b ∧ b - 1 ∈ IsLocalRing.maximalIdeal B ^ y ∧
      a - ∏ᶠ σ : G, σ • b ∈ IsLocalRing.maximalIdeal B ^ (Nat.card G * (y + 1)) := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  let A := FixedPoints.subring B G
  haveI : IsDiscreteValuationRing A := FixedPoints.isDiscreteValuationRing_subring
  letI : Field (A ⧸ IsLocalRing.maximalIdeal A) := Ideal.Quotient.field _
  letI : Field (B ⧸ IsLocalRing.maximalIdeal B) := Ideal.Quotient.field _
  haveI : Finite (A ⧸ IsLocalRing.maximalIdeal A) :=
    Finite.of_injective _ (algebraMap (A ⧸ IsLocalRing.maximalIdeal A) (B ⧸ IsLocalRing.maximalIdeal B)).injective
  have ht1 : 1 ≤ t := by omega

  have hℓB : (Nat.card G : B) ∈ IsLocalRing.maximalIdeal B := natCast_card_mem_maximalIdeal hℓ ht1 ht
  have hℓA : (Nat.card G : A) ∈ IsLocalRing.maximalIdeal A := by
    rw [FixedPoints.mem_maximalIdeal_subring_iff]; push_cast; exact hℓB
  have hℓk : ((Nat.card G : ℕ) : A ⧸ IsLocalRing.maximalIdeal A) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)), Ideal.Quotient.eq_zero_iff_mem]
    exact hℓA
  have hsurj := pow_surjective_of_natCast_eq_zero (k := A ⧸ IsLocalRing.maximalIdeal A) hℓ hℓk
  obtain ⟨π, ϖ, hπ, hϖG, hϖdef, hϖm, hdiv⟩ := exists_uniformizer_package (B := B) (G := G) ht
  have hπm : π ∈ IsLocalRing.maximalIdeal B := hπ.not_isUnit

  have hlift : ∀ β : B, (∀ σ : G, σ • β = β) → ∃ u : B, (∀ σ : G, σ • u = u) ∧
      β - u ^ Nat.card G ∈ IsLocalRing.maximalIdeal B ^ Nat.card G ∧ (IsUnit β → IsUnit u) := by
    intro β hβG
    let βA : A := ⟨β, hβG⟩
    obtain ⟨ubar, hubar⟩ := hsurj (Ideal.Quotient.mk _ βA)
    obtain ⟨uA, rfl⟩ := Ideal.Quotient.mk_surjective ubar
    have hdiff : βA - uA ^ Nat.card G ∈ IsLocalRing.maximalIdeal A := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow]
      exact sub_eq_zero.mpr hubar.symm
    refine ⟨(uA : B), uA.2, ?_, ?_⟩
    · have h := mem_maximalIdeal_pow_card_of_forall_smul_eq (G := G) ht (x := ((βA - uA ^ Nat.card G : A) : B))
        (βA - uA ^ Nat.card G).2 (FixedPoints.mem_maximalIdeal_subring_iff.mp hdiff)
      simpa using h
    · intro hβu
      have hβA : IsUnit βA := (FixedPoints.isUnit_subring_iff βA).mpr hβu
      have huA : IsUnit uA := by
        by_contra hu
        have hum : uA ∈ IsLocalRing.maximalIdeal A := (IsLocalRing.mem_maximalIdeal _).mpr hu
        have : βA ∈ IsLocalRing.maximalIdeal A := by
          have := Submodule.add_mem _ hdiff (Ideal.pow_mem_of_mem _ hum (Nat.card G) Nat.card_pos)
          rwa [sub_add_cancel] at this
        exact (IsLocalRing.mem_maximalIdeal _).mp this hβA
      exact (FixedPoints.isUnit_subring_iff uA).mp huA
  rcases Nat.eq_zero_or_pos y with rfl | hy0
  ·
    obtain ⟨u, huG, hau', huu⟩ := hlift a haG
    refine ⟨u, huu hau, by simp, ?_⟩
    rw [finprod_smul_of_forall_smul_eq huG, zero_add, mul_one]
    simpa using hau'
  ·
    obtain ⟨β, hβG, hαβ⟩ := hdiv y (a - 1) (fun σ => by rw [smul_sub, haG, smul_one]) ha
    obtain ⟨u, huG, hβu, -⟩ := hlift β hβG
    set x := u * π ^ y with hxdef
    have hxm : x ∈ IsLocalRing.maximalIdeal B ^ y := Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow hπm y)
    have hx1 : x ∈ IsLocalRing.maximalIdeal B := by
      have := Ideal.pow_le_self (Nat.pos_iff_ne_zero.mp hy0) hxm; exact this
    refine ⟨1 + x, isUnit_one_add_of_mem hx1, by rw [add_sub_cancel_left]; exact hxm, ?_⟩

    have hN1x : (∏ᶠ σ : G, σ • (1 + x)) = ∏ᶠ σ : G, (1 + σ • x) :=
      finprod_congr fun σ => by rw [smul_add, smul_one]
    have hcore := finprod_one_add_smul_sub_one_sub_finprod_mem hℓ t ht ht' y hy x hxm
    have hNx : ∏ᶠ σ : G, σ • x = u ^ Nat.card G * ϖ ^ y := by
      rw [hxdef, finprod_smul_mul, finprod_smul_of_forall_smul_eq huG, hϖdef]
      congr 1
      simp only [finprod_eq_prod_of_fintype, smul_pow', Finset.prod_pow]
    have key : a - ∏ᶠ σ : G, σ • (1 + x) =
        ϖ ^ y * (β - u ^ Nat.card G) - ((∏ᶠ σ : G, (1 + σ • x)) - 1 - ∏ᶠ σ : G, σ • x) := by
      rw [hN1x, hNx]
      have : a = 1 + ϖ ^ y * β := by rw [← hαβ]; ring
      rw [this]; ring
    rw [key]
    refine Submodule.sub_mem _ ?_ hcore
    have hϖy : ϖ ^ y ∈ IsLocalRing.maximalIdeal B ^ (Nat.card G * y) := by
      have := Ideal.pow_mem_pow hϖm y; rwa [← pow_mul] at this
    rw [Nat.mul_succ, pow_add]
    exact Ideal.mul_mem_mul hϖy hβu

end belowmain

section jumpmain
variable {B : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable {G : Type*} [Group G] [Finite G] [MulSemiringAction G B] [FaithfulSMul G B]
variable [(IsLocalRing.maximalIdeal B).LiesOver (IsLocalRing.maximalIdeal (FixedPoints.subring B G))]
variable [Algebra.IsSeparable
      (FixedPoints.subring B G ⧸ IsLocalRing.maximalIdeal (FixedPoints.subring B G))
      (B ⧸ IsLocalRing.maximalIdeal B)]

theorem exists_finset_reps_of_card_ker_le {M : Type*} [AddCommGroup M] [Finite M] (f : M →+ M) (ℓ : ℕ)
    (hker : Nat.card f.ker ≤ ℓ) :
    ∃ T : Finset M, T.card ≤ ℓ ∧ ∀ m : M, ∃ r ∈ T, ∃ u : M, m = r + f u := by
  classical
  haveI : Fintype M := Fintype.ofFinite M
  haveI : Fintype (M ⧸ f.range) := Fintype.ofFinite _

  have hquot : Nat.card (M ⧸ f.range) = Nat.card f.ker := by
    have h1 : Nat.card M = Nat.card (M ⧸ f.range) * Nat.card f.range := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup _
    have h2 : Nat.card M = Nat.card (M ⧸ f.ker) * Nat.card f.ker := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup _
    have h3 : Nat.card (M ⧸ f.ker) = Nat.card f.range := Nat.card_congr (QuotientAddGroup.quotientKerEquivRange f).toEquiv
    rw [h3, mul_comm] at h2
    have hpos : 0 < Nat.card f.range := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hpos (h1.symm.trans h2)
  refine ⟨Finset.univ.image (fun q : M ⧸ f.range => Quotient.out q), ?_, ?_⟩
  · calc (Finset.univ.image (fun q : M ⧸ f.range => Quotient.out q)).card ≤ (Finset.univ : Finset (M ⧸ f.range)).card :=
          Finset.card_image_le
      _ = Nat.card (M ⧸ f.range) := by rw [Finset.card_univ, Nat.card_eq_fintype_card]
      _ ≤ ℓ := hquot ▸ hker
  · intro m
    refine ⟨Quotient.out (QuotientAddGroup.mk m : M ⧸ f.range), Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩
    have h : (QuotientAddGroup.mk (Quotient.out (QuotientAddGroup.mk m : M ⧸ f.range)) : M ⧸ f.range) = QuotientAddGroup.mk m :=
      QuotientAddGroup.out_eq' _
    rw [QuotientAddGroup.eq] at h
    obtain ⟨u, hu⟩ := h
    exact ⟨u, by rw [hu]; abel⟩

theorem exists_finset_reps_of_card_ker_le_mul {M : Type*} [CommGroup M] [Finite M] (f : M →* M) (ℓ : ℕ)
    (hker : Nat.card f.ker ≤ ℓ) :
    ∃ T : Finset M, T.card ≤ ℓ ∧ ∀ m : M, ∃ r ∈ T, ∃ u : M, m = r * f u := by
  classical
  haveI : Fintype M := Fintype.ofFinite M
  haveI : Fintype (M ⧸ f.range) := Fintype.ofFinite _
  have hquot : Nat.card (M ⧸ f.range) = Nat.card f.ker := by
    have h1 : Nat.card M = Nat.card (M ⧸ f.range) * Nat.card f.range := Subgroup.card_eq_card_quotient_mul_card_subgroup _
    have h2 : Nat.card M = Nat.card (M ⧸ f.ker) * Nat.card f.ker := Subgroup.card_eq_card_quotient_mul_card_subgroup _
    have h3 : Nat.card (M ⧸ f.ker) = Nat.card f.range := Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
    rw [h3, mul_comm] at h2
    have hpos : 0 < Nat.card f.range := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hpos (h1.symm.trans h2)
  refine ⟨Finset.univ.image (fun q : M ⧸ f.range => Quotient.out q), ?_, ?_⟩
  · calc (Finset.univ.image (fun q : M ⧸ f.range => Quotient.out q)).card ≤ (Finset.univ : Finset (M ⧸ f.range)).card :=
          Finset.card_image_le
      _ = Nat.card (M ⧸ f.range) := by rw [Finset.card_univ, Nat.card_eq_fintype_card]
      _ ≤ ℓ := hquot ▸ hker
  · intro m
    refine ⟨Quotient.out (QuotientGroup.mk m : M ⧸ f.range), Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩
    have h : (QuotientGroup.mk (Quotient.out (QuotientGroup.mk m : M ⧸ f.range)) : M ⧸ f.range) = QuotientGroup.mk m :=
      QuotientGroup.out_eq' _
    rw [QuotientGroup.eq] at h
    obtain ⟨u, hu⟩ := h
    exact ⟨u, by rw [hu, ← mul_assoc, mul_inv_cancel, one_mul]⟩

theorem card_ker_frobenius_add_le {k : Type*} [Field k] [Finite k] {ℓ : ℕ} (hℓ : ℓ.Prime) [CharP k ℓ] (c : k) :
    ∃ f : k →+ k, (∀ ξ, f ξ = ξ ^ ℓ + c * ξ) ∧ Nat.card f.ker ≤ ℓ := by
  classical
  haveI := Fact.mk hℓ
  let f : k →+ k :=
    { toFun := fun ξ => ξ ^ ℓ + c * ξ
      map_zero' := by simp [hℓ.ne_zero]
      map_add' := fun x y => by rw [add_pow_char, mul_add]; ring }
  refine ⟨f, fun ξ => rfl, ?_⟩

  let p : Polynomial k := Polynomial.X ^ ℓ + Polynomial.C c * Polynomial.X
  have hq : (Polynomial.C c * Polynomial.X).degree < (ℓ : WithBot ℕ) :=
    calc (Polynomial.C c * Polynomial.X).degree ≤ (Polynomial.C c).degree + Polynomial.X.degree := Polynomial.degree_mul_le _ _
      _ ≤ 0 + 1 := add_le_add Polynomial.degree_C_le Polynomial.degree_X_le
      _ < ℓ := by rw [zero_add]; exact_mod_cast hℓ.one_lt
  have hp : p.Monic := Polynomial.monic_X_pow_add hq
  have hp0 : p ≠ 0 := hp.ne_zero
  have hdeg : p.natDegree ≤ ℓ := by
    refine (Polynomial.natDegree_add_le _ _).trans (max_le (by rw [Polynomial.natDegree_X_pow]) ?_)
    calc (Polynomial.C c * Polynomial.X).natDegree ≤ (Polynomial.C c).natDegree + Polynomial.X.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 0 + 1 := add_le_add (Polynomial.natDegree_C c).le Polynomial.natDegree_X_le
      _ ≤ ℓ := by rw [zero_add]; exact hℓ.one_lt.le
  have hsub : ∀ ξ : k, f ξ = 0 → ξ ∈ p.roots.toFinset := fun ξ h => by
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hp0, Polynomial.IsRoot, Polynomial.eval_add, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    exact h
  let g : f.ker → ↥p.roots.toFinset := fun ξ => ⟨ξ.1, hsub ξ.1 ξ.2⟩
  have hg : Function.Injective g := fun ξ₁ ξ₂ h => Subtype.ext (by simpa [g] using congrArg Subtype.val h)
  calc Nat.card f.ker ≤ Nat.card ↥p.roots.toFinset := Nat.card_le_card_of_injective g hg
    _ = p.roots.toFinset.card := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ ≤ Multiset.card p.roots := Multiset.toFinset_card_le _
    _ ≤ p.natDegree := Polynomial.card_roots' p
    _ ≤ ℓ := hdeg

theorem card_ker_powMonoidHom_le {k : Type*} [Field k] [Finite k] {ℓ : ℕ} (hℓ : ℓ.Prime) :
    Nat.card (powMonoidHom ℓ : kˣ →* kˣ).ker ≤ ℓ := by
  classical
  have hsub : ∀ u : kˣ, u ^ ℓ = 1 → (u : k) ∈ (Polynomial.nthRoots ℓ (1 : k)).toFinset := fun u h => by
    rw [Multiset.mem_toFinset, Polynomial.mem_nthRoots hℓ.pos, ← Units.val_pow_eq_pow_val, h, Units.val_one]
  let g : (powMonoidHom ℓ : kˣ →* kˣ).ker → ↥(Polynomial.nthRoots ℓ (1 : k)).toFinset :=
    fun u => ⟨(u.1 : k), hsub u.1 (by have := u.2; rwa [MonoidHom.mem_ker, powMonoidHom_apply] at this)⟩
  have hg : Function.Injective g := fun u₁ u₂ h => Subtype.ext (Units.ext (by simpa [g] using congrArg Subtype.val h))
  calc Nat.card (powMonoidHom ℓ : kˣ →* kˣ).ker ≤ Nat.card ↥(Polynomial.nthRoots ℓ (1 : k)).toFinset :=
        Nat.card_le_card_of_injective g hg
    _ = (Polynomial.nthRoots ℓ (1 : k)).toFinset.card := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ ≤ Multiset.card (Polynomial.nthRoots ℓ (1 : k)) := Multiset.toFinset_card_le _
    _ ≤ ℓ := Polynomial.card_nthRoots ℓ 1

end jumpmain

section jumpcases
variable {B : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable {G : Type*} [Group G] [Finite G] [MulSemiringAction G B] [FaithfulSMul G B]
variable [(IsLocalRing.maximalIdeal B).LiesOver (IsLocalRing.maximalIdeal (FixedPoints.subring B G))]
variable [Algebra.IsSeparable
      (FixedPoints.subring B G ⧸ IsLocalRing.maximalIdeal (FixedPoints.subring B G))
      (B ⧸ IsLocalRing.maximalIdeal B)]

theorem exists_finset_of_eq_jump_wild (hℓ : (Nat.card G).Prime) (t : ℕ) (ht1 : 1 ≤ t)
    (ht : IsLocalRing.lowerRamificationGroup B G t = ⊤) (ht' : IsLocalRing.lowerRamificationGroup B G (t + 1) = ⊥)
    [Finite (B ⧸ IsLocalRing.maximalIdeal B)] :
    ∃ S : Finset B, S.card ≤ Nat.card G ∧
      (∀ s ∈ S, IsUnit s ∧ (∀ σ : G, σ • s = s) ∧ s - 1 ∈ IsLocalRing.maximalIdeal B ^ (Nat.card G * t)) ∧
      ∀ a : B, IsUnit a → (∀ σ : G, σ • a = a) → a - 1 ∈ IsLocalRing.maximalIdeal B ^ (Nat.card G * t) →
        ∃ s ∈ S, ∃ b : B, IsUnit b ∧ b - 1 ∈ IsLocalRing.maximalIdeal B ^ t ∧
          a - s * ∏ᶠ σ : G, σ • b ∈ IsLocalRing.maximalIdeal B ^ (Nat.card G * (t + 1)) := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  let A := FixedPoints.subring B G
  haveI : IsDiscreteValuationRing A := FixedPoints.isDiscreteValuationRing_subring
  letI : Field (A ⧸ IsLocalRing.maximalIdeal A) := Ideal.Quotient.field _
  letI : Field (B ⧸ IsLocalRing.maximalIdeal B) := Ideal.Quotient.field _
  haveI : Finite (A ⧸ IsLocalRing.maximalIdeal A) :=
    Finite.of_injective _ (algebraMap (A ⧸ IsLocalRing.maximalIdeal A) (B ⧸ IsLocalRing.maximalIdeal B)).injective

  have hℓB : (Nat.card G : B) ∈ IsLocalRing.maximalIdeal B := natCast_card_mem_maximalIdeal hℓ ht1 ht
  have hℓA : (Nat.card G : A) ∈ IsLocalRing.maximalIdeal A := by
    rw [FixedPoints.mem_maximalIdeal_subring_iff]; push_cast; exact hℓB
  have hℓk : ((Nat.card G : ℕ) : A ⧸ IsLocalRing.maximalIdeal A) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)), Ideal.Quotient.eq_zero_iff_mem]
    exact hℓA
  haveI := Fact.mk hℓ
  haveI : CharP (A ⧸ IsLocalRing.maximalIdeal A) (Nat.card G) :=
    ringChar.eq_iff.mp (CharP.ringChar_of_prime_eq_zero hℓ hℓk)

  obtain ⟨π, ϖ, hπ, hϖG, hϖdef, hϖm, hdiv⟩ := exists_uniformizer_package (B := B) (G := G) ht
  have hπm : π ∈ IsLocalRing.maximalIdeal B := hπ.not_isUnit
  have hϖy : ∀ y : ℕ, ϖ ^ y ∈ IsLocalRing.maximalIdeal B ^ (Nat.card G * y) := fun y => by
    have := Ideal.pow_mem_pow hϖm y; rwa [← pow_mul] at this
  have hϖ1 : ϖ ∈ IsLocalRing.maximalIdeal B := Ideal.pow_le_self hℓ.ne_zero hϖm
  have hTrG : ∀ τ : G, τ • ∑ᶠ σ : G, σ • π ^ t = ∑ᶠ σ : G, σ • π ^ t := fun τ => smul_finsum_smul τ (π ^ t)
  have hTrm : ∑ᶠ σ : G, σ • π ^ t ∈ IsLocalRing.maximalIdeal B ^ (Nat.card G * t) :=
    finsum_smul_mem_of_mem_pow_jump hℓ t ht1 ht ht' (π ^ t) (Ideal.pow_mem_pow hπm t)
  obtain ⟨c, hcG, hTrc⟩ := hdiv t _ hTrG hTrm
  let cA : A := ⟨c, hcG⟩

  obtain ⟨f, hf, hker⟩ := card_ker_frobenius_add_le (k := A ⧸ IsLocalRing.maximalIdeal A) hℓ (Ideal.Quotient.mk _ cA)
  obtain ⟨T, hTcard, hT⟩ := exists_finset_reps_of_card_ker_le f (Nat.card G) hker
  have hL : ∀ ξ : A ⧸ IsLocalRing.maximalIdeal A, ∃ r : A, Ideal.Quotient.mk _ r = ξ := Ideal.Quotient.mk_surjective
  choose L hL using hL
  refine ⟨T.image (fun ξ => 1 + ϖ ^ t * (L ξ : B)), Finset.card_image_le.trans hTcard, ?_, ?_⟩
  · intro s hs
    obtain ⟨ξ, -, rfl⟩ := Finset.mem_image.mp hs
    refine ⟨isUnit_one_add_of_mem (Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ hϖ1 t ht1)), fun σ => ?_, ?_⟩
    · rw [smul_add, smul_one, smul_mul', smul_pow', hϖG, (L ξ).2]
    · rw [add_sub_cancel_left]; exact Ideal.mul_mem_right _ _ (hϖy t)
  · intro a hau haG ha
    obtain ⟨β, hβG, hαβ⟩ := hdiv t (a - 1) (fun σ => by rw [smul_sub, haG, smul_one]) ha
    let βA : A := ⟨β, hβG⟩
    obtain ⟨r, hrT, ubar, hrep⟩ := hT (Ideal.Quotient.mk _ βA)
    obtain ⟨uA, huA⟩ := Ideal.Quotient.mk_surjective ubar
    set x : B := (uA : B) * π ^ t with hxdef
    have hxm : x ∈ IsLocalRing.maximalIdeal B ^ t := Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow hπm t)
    have hx1 : x ∈ IsLocalRing.maximalIdeal B := Ideal.pow_le_self (by omega) hxm
    refine ⟨1 + ϖ ^ t * (L r : B), Finset.mem_image_of_mem _ hrT, 1 + x, isUnit_one_add_of_mem hx1,
      by rw [add_sub_cancel_left]; exact hxm, ?_⟩
    have hN1x : (∏ᶠ σ : G, σ • (1 + x)) = ∏ᶠ σ : G, (1 + σ • x) :=
      finprod_congr fun σ => by rw [smul_add, smul_one]
    have hcore := finprod_one_add_smul_sub_one_sub_finsum_sub_finprod_mem hℓ t ht1 ht ht' x hxm
    have hTrx : ∑ᶠ σ : G, σ • x = (uA : B) * (ϖ ^ t * c) := by
      rw [hxdef, finsum_smul_mul_of_forall_smul_eq uA.2 (π ^ t), hTrc]
    have hNx : ∏ᶠ σ : G, σ • x = (uA : B) ^ Nat.card G * ϖ ^ t := by
      rw [hxdef, finprod_smul_mul, finprod_smul_of_forall_smul_eq uA.2, hϖdef]
      congr 1
      simp only [finprod_eq_prod_of_fintype, smul_pow', Finset.prod_pow]

    have key : a - (1 + ϖ ^ t * (L r : B)) * ∏ᶠ σ : G, σ • (1 + x) =
        ϖ ^ t * (β - (L r : B) - c * (uA : B) - (uA : B) ^ Nat.card G)
          - ϖ ^ t * ϖ ^ t * ((L r : B) * (c * (uA : B) + (uA : B) ^ Nat.card G))
          - (1 + ϖ ^ t * (L r : B)) * ((∏ᶠ σ : G, (1 + σ • x)) - 1 - ∑ᶠ σ : G, σ • x - ∏ᶠ σ : G, σ • x) := by
      rw [hN1x]
      have ha1 : a = 1 + ϖ ^ t * β := by rw [← hαβ]; ring
      rw [ha1, hTrx, hNx]; ring
    rw [key]
    refine Submodule.sub_mem _ (Submodule.sub_mem _ ?_ ?_) (Ideal.mul_mem_left _ _ hcore)
    ·
      have hδA : (βA - L r - cA * uA - uA ^ Nat.card G : A) ∈ IsLocalRing.maximalIdeal A := by
        rw [← Ideal.Quotient.eq_zero_iff_mem]
        simp only [map_sub, map_mul, map_pow, hL r, huA, hrep, hf]
        ring
      have hδB := mem_maximalIdeal_pow_card_of_forall_smul_eq (G := G) ht
        (x := ((βA - L r - cA * uA - uA ^ Nat.card G : A) : B)) (βA - L r - cA * uA - uA ^ Nat.card G).2
        (FixedPoints.mem_maximalIdeal_subring_iff.mp hδA)
      have hδB' : β - (L r : B) - c * (uA : B) - (uA : B) ^ Nat.card G ∈ IsLocalRing.maximalIdeal B ^ Nat.card G := by
        simpa using hδB
      rw [Nat.mul_succ, pow_add]
      exact Ideal.mul_mem_mul (hϖy t) hδB'
    · refine Ideal.mul_mem_right _ _ ?_
      have h2 : ϖ ^ t * ϖ ^ t ∈ IsLocalRing.maximalIdeal B ^ (Nat.card G * t + Nat.card G * t) := by
        rw [pow_add]; exact Ideal.mul_mem_mul (hϖy t) (hϖy t)
      exact Ideal.pow_le_pow_right (by nlinarith) h2

theorem exists_finset_of_jump_zero (hℓ : (Nat.card G).Prime)
    (ht : IsLocalRing.lowerRamificationGroup B G 0 = ⊤)
    [Finite (B ⧸ IsLocalRing.maximalIdeal B)] :
    ∃ S : Finset B, S.card ≤ Nat.card G ∧ (∀ s ∈ S, IsUnit s ∧ (∀ σ : G, σ • s = s)) ∧
      ∀ a : B, IsUnit a → (∀ σ : G, σ • a = a) →
        ∃ s ∈ S, ∃ b : B, IsUnit b ∧ a - s * ∏ᶠ σ : G, σ • b ∈ IsLocalRing.maximalIdeal B ^ Nat.card G := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  let A := FixedPoints.subring B G
  haveI : IsDiscreteValuationRing A := FixedPoints.isDiscreteValuationRing_subring
  letI : Field (A ⧸ IsLocalRing.maximalIdeal A) := Ideal.Quotient.field _
  letI : Field (B ⧸ IsLocalRing.maximalIdeal B) := Ideal.Quotient.field _
  haveI : Finite (A ⧸ IsLocalRing.maximalIdeal A) :=
    Finite.of_injective _ (algebraMap (A ⧸ IsLocalRing.maximalIdeal A) (B ⧸ IsLocalRing.maximalIdeal B)).injective
  let k := A ⧸ IsLocalRing.maximalIdeal A
  obtain ⟨T, hTcard, hT⟩ := exists_finset_reps_of_card_ker_le_mul (powMonoidHom (Nat.card G) : kˣ →* kˣ) (Nat.card G)
    (card_ker_powMonoidHom_le hℓ)
  have hL : ∀ ξ : k, ∃ r : A, Ideal.Quotient.mk _ r = ξ := Ideal.Quotient.mk_surjective
  choose L hL using hL

  have hLu : ∀ ξ : k, ξ ≠ 0 → IsUnit (L ξ : B) := fun ξ hξ => by
    have : IsUnit (L ξ) := by
      by_contra h
      have hm : L ξ ∈ IsLocalRing.maximalIdeal A := (IsLocalRing.mem_maximalIdeal _).mpr h
      rw [← Ideal.Quotient.eq_zero_iff_mem, hL] at hm
      exact hξ hm
    exact (FixedPoints.isUnit_subring_iff _).mp this
  refine ⟨T.image (fun r : kˣ => (L (r : k) : B)), Finset.card_image_le.trans hTcard, ?_, ?_⟩
  · intro s hs
    obtain ⟨r, -, rfl⟩ := Finset.mem_image.mp hs
    exact ⟨hLu _ r.ne_zero, (L (r : k)).2⟩
  · intro a hau haG
    let aA : A := ⟨a, haG⟩
    have haA : IsUnit aA := (FixedPoints.isUnit_subring_iff aA).mpr hau
    have ha0 : Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) aA ≠ 0 := by
      rw [ne_eq, Ideal.Quotient.eq_zero_iff_mem]
      exact fun h => (IsLocalRing.mem_maximalIdeal _).mp h haA
    obtain ⟨r, hrT, ubar, hrep⟩ := hT (Units.mk0 _ ha0)
    have hu0 : ((ubar : kˣ) : k) ≠ 0 := ubar.ne_zero
    refine ⟨(L (r : k) : B), Finset.mem_image_of_mem _ hrT, (L (ubar : k) : B), hLu _ hu0, ?_⟩
    rw [finprod_smul_of_forall_smul_eq (L (ubar : k)).2]
    have hrep' : Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) aA = (r : k) * ((ubar : kˣ) : k) ^ Nat.card G := by
      have := congrArg (fun z : kˣ => (z : k)) hrep
      simpa [Units.val_mul, Units.val_pow_eq_pow_val] using this
    have hδA : (aA - L (r : k) * L (ubar : k) ^ Nat.card G : A) ∈ IsLocalRing.maximalIdeal A := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      simp only [map_sub, map_mul, map_pow, hL, hrep', sub_self]
    have hδB := mem_maximalIdeal_pow_card_of_forall_smul_eq (G := G) ht
      (x := ((aA - L (r : k) * L (ubar : k) ^ Nat.card G : A) : B)) (aA - L (r : k) * L (ubar : k) ^ Nat.card G).2
      (FixedPoints.mem_maximalIdeal_subring_iff.mp hδA)
    simpa using hδB

end jumpcases

end IsDiscreteValuationRing.XCGrCoker

open IsDiscreteValuationRing.XCGrCoker in

theorem solution
    {B : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G B] [FaithfulSMul G B]
    [(IsLocalRing.maximalIdeal B).LiesOver (IsLocalRing.maximalIdeal (FixedPoints.subring B G))]
    [Algebra.IsSeparable
      (FixedPoints.subring B G ⧸ IsLocalRing.maximalIdeal (FixedPoints.subring B G))
      (B ⧸ IsLocalRing.maximalIdeal B)]
    [Finite (B ⧸ IsLocalRing.maximalIdeal B)]
    (hℓ : (Nat.card G).Prime) (t : ℕ)
    (ht : IsLocalRing.lowerRamificationGroup B G t = ⊤) (ht' : IsLocalRing.lowerRamificationGroup B G (t + 1) = ⊥)
    (y : ℕ) :
    ∃ S : Finset B, S.card ≤ (if y = t then Nat.card G else 1) ∧
      (∀ s ∈ S, IsUnit s ∧ (∀ σ : G, σ • s = s) ∧ s - 1 ∈ IsLocalRing.maximalIdeal B ^ (Nat.card G * y)) ∧
      ∀ a : B, IsUnit a → (∀ σ : G, σ • a = a) → a - 1 ∈ IsLocalRing.maximalIdeal B ^ (Nat.card G * y) →
        ∃ s ∈ S, ∃ b : B, IsUnit b ∧
          b - 1 ∈ IsLocalRing.maximalIdeal B ^ (if y ≤ t then y else t + Nat.card G * (y - t)) ∧
          a - s * ∏ᶠ σ : G, σ • b ∈ IsLocalRing.maximalIdeal B ^ (Nat.card G * (y + 1)) := by
  classical
  rcases lt_trichotomy y t with hlt | rfl | hgt
  ·
    refine ⟨{1}, by rw [if_neg hlt.ne, Finset.card_singleton], ?_, ?_⟩
    · intro s hs
      rw [Finset.mem_singleton] at hs; subst hs
      exact ⟨isUnit_one, fun σ => smul_one σ, by rw [sub_self]; exact Submodule.zero_mem _⟩
    · intro a hau haG ha
      obtain ⟨b, hbu, hb1, hab⟩ := exists_finprod_smul_sub_mem_of_lt_jump hℓ t ht ht' y hlt a hau haG ha
      refine ⟨1, Finset.mem_singleton_self 1, b, hbu, by rw [if_pos hlt.le]; exact hb1, by rw [one_mul]; exact hab⟩
  ·
    rw [if_pos rfl, if_pos le_rfl]
    rcases Nat.eq_zero_or_pos y with rfl | hy1
    · obtain ⟨S, hScard, hS, hmain⟩ := exists_finset_of_jump_zero (B := B) (G := G) hℓ ht
      refine ⟨S, hScard, fun s hs => ⟨(hS s hs).1, (hS s hs).2, by rw [mul_zero, pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top⟩, ?_⟩
      intro a hau haG _
      obtain ⟨s, hs, b, hbu, hab⟩ := hmain a hau haG
      exact ⟨s, hs, b, hbu, by rw [pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top, by rw [zero_add, mul_one]; exact hab⟩
    · exact exists_finset_of_eq_jump_wild hℓ y hy1 ht ht'
  ·
    refine ⟨{1}, by rw [if_neg hgt.ne', Finset.card_singleton], ?_, ?_⟩
    · intro s hs
      rw [Finset.mem_singleton] at hs; subst hs
      exact ⟨isUnit_one, fun σ => smul_one σ, by rw [sub_self]; exact Submodule.zero_mem _⟩
    · intro a hau haG ha
      obtain ⟨b, hb1, hab⟩ :=
        IsDiscreteValuationRing.exists_sub_one_mem_and_finprod_smul_sub_mem_of_jump_lt_of_prime_card
          hℓ t ht ht' y hgt ⟨a, haG⟩ ha
      have hb1' : b - 1 ∈ IsLocalRing.maximalIdeal B := by
        refine Ideal.pow_le_self ?_ hb1
        have : 0 < Nat.card G := Nat.card_pos
        have : 0 < Nat.card G * (y - t) := Nat.mul_pos this (by omega)
        omega
      refine ⟨1, Finset.mem_singleton_self 1, b, ?_, by rw [if_neg (not_le.mpr hgt)]; exact hb1, ?_⟩
      · have := isUnit_one_add_of_mem hb1'; rwa [add_sub_cancel] at this
      · rw [one_mul, ← neg_sub]
        exact Submodule.neg_mem _ hab

end S_IsDiscreteValuationRing_exists_finset_card_le_forall_exists_sub_mul_finprod_smul_mem_pow_of_prime_card
end P2MW
export P2MW.S_IsDiscreteValuationRing_exists_finset_card_le_forall_exists_sub_mul_finprod_smul_mem_pow_of_prime_card (solution)
