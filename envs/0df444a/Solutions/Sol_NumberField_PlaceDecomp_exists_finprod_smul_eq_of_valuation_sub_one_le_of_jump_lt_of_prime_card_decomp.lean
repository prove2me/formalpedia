-- Prove2me | solution 1 for NumberField.PlaceDecomp.exists_finprod_smul_eq_of_valuation_sub_one_le_of_jump_lt_of_prime_card_decomp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/e5bb7e8a-e2f3-5a41-a8d9-8212573ffa02

import Mathlib
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup
import Definitions.Def_Mathlib_RingTheory_Invariant_FixedSubringLocal
import Definitions.Def_Mathlib_RingTheory_Invariant_FixedSubringGaloisGroup
import Definitions.Def_DifferentFiltrationMonogenicDischarge
import Theorems.Thm_FixedPoints_isDiscreteValuationRing_subring
import Theorems.Thm_IsDiscreteValuationRing_addVal_coe_eq_lowerRamificationCard_zero_mul_addVal_fixedPoints
import Theorems.Thm_IsDiscreteValuationRing_exists_adjoin_singleton_eq_top_of_isSeparable_residueField
import Theorems.Thm_NumberField_PlaceDecomp_forall_smul_eq_iff_mem_range_adicCompletionSemialgHom
import Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_map_subtype_inertiaSubgroup_valuationSubring_eq_inertia
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_PlaceDecomp_exists_finprod_smul_eq_of_valuation_sub_one_le_of_jump_lt_of_prime_card_decomp
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxSynthPendingDepth 3
p2m_open "IsDedekindDomain NumberField P2MW.S_NumberField_PlaceDecomp_exists_finprod_smul_eq_of_valuation_sub_one_le_of_jump_lt_of_prime_card_decomp.NumberField"
p2m_open_scoped "NumberField.PlaceDecomp P2MW.S_NumberField_PlaceDecomp_exists_finprod_smul_eq_of_valuation_sub_one_le_of_jump_lt_of_prime_card_decomp.NumberField.PlaceDecomp"

section CL2_inlined

namespace Ws45
namespace CL2

open scoped Pointwise

variable {B : Type*} [CommRing B] {G : Type*} [Group G] [MulSemiringAction G B]

theorem exists_sum_eq_sum_smul_of_free [Fintype G] {X : Type*} [Fintype X] [MulAction G X]
    (hfree : ∀ (τ : G) (x : X), τ • x = x → τ = 1) (g : X → B) (hg : ∀ (τ : G) (x : X), g (τ • x) = τ • g x)
    (P : B → Prop) (hP0 : P 0) (hPadd : ∀ a b, P a → P b → P (a + b)) (hPg : ∀ x, P (g x)) :
    ∃ R : B, P R ∧ ∑ x, g x = ∑ τ : G, τ • R := by
  classical
  let Ω := MulAction.orbitRel.Quotient G X
  haveI : Fintype Ω := Quotient.fintype _

  let e : G × Ω → X := fun p => p.1 • p.2.out
  have hmk : ∀ (τ : G) (x : X), (Quotient.mk (MulAction.orbitRel G X) (τ • x) : Ω) = Quotient.mk _ x :=
    fun τ x => Quotient.sound ⟨τ, rfl⟩
  have hinj : Function.Injective e := by
    rintro ⟨τ, a⟩ ⟨τ', b⟩ h
    simp only [e] at h
    have hab : a = b := by
      have h1 := hmk τ a.out
      have h2 := hmk τ' b.out
      rw [Quotient.out_eq] at h1 h2
      rw [← h1, ← h2, h]
    subst hab
    have : (τ'⁻¹ * τ) • a.out = a.out := by rw [mul_smul, h, inv_smul_smul]
    have := hfree _ _ this
    rw [inv_mul_eq_one] at this
    rw [this]
  have hsurj : Function.Surjective e := by
    intro x
    obtain ⟨τ, hτ⟩ : ∃ τ : G, τ • x = (Quotient.mk (MulAction.orbitRel G X) x : Ω).out :=
      Quotient.exact (Quotient.out_eq (Quotient.mk (MulAction.orbitRel G X) x : Ω))
    refine ⟨(τ⁻¹, Quotient.mk _ x), ?_⟩
    simp only [e]
    rw [← hτ, inv_smul_smul]
  let eqv : G × Ω ≃ X := Equiv.ofBijective e ⟨hinj, hsurj⟩
  refine ⟨∑ ω : Ω, g ω.out, ?_, ?_⟩
  · exact Finset.sum_induction _ P hPadd hP0 fun ω _ => hPg _
  · rw [← Equiv.sum_comp eqv g, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun ω _ => ?_
    exact hg τ ω.out

variable [Fintype G] [DecidableEq G]

abbrev Sub (j : ℕ) : Type _ := {t : Finset G // t.card = j}

scoped instance (j : ℕ) : MulAction G (Sub (G := G) j) where
  smul τ t := ⟨τ • t.1, by rw [Finset.card_smul_finset]; exact t.2⟩
  one_smul t := Subtype.ext (one_smul G t.1)
  mul_smul τ τ' t := Subtype.ext (mul_smul τ τ' t.1)

omit [Fintype G] in
theorem coe_smul_sub {j : ℕ} (τ : G) (t : Sub (G := G) j) : ((τ • t : Sub (G := G) j) : Finset G) = τ • (t : Finset G) := rfl

theorem smul_sub_free (hℓ : (Nat.card G).Prime) {j : ℕ} (hj0 : 0 < j) (hjℓ : j < Nat.card G)
    (τ : G) (t : Sub (G := G) j) (h : τ • t = t) : τ = 1 := by
  by_contra hτ
  have ht : τ • (t : Finset G) = t := congrArg Subtype.val h

  have hstab : ∀ ρ : G, ρ • (t : Finset G) = t := by
    haveI := Fact.mk hℓ
    have htop : Subgroup.zpowers τ = ⊤ := zpowers_eq_top_of_prime_card rfl hτ
    have hle : Subgroup.zpowers τ ≤ MulAction.stabilizer G (t : Finset G) := by
      rw [Subgroup.zpowers_le]; exact ht
    rw [htop, top_le_iff] at hle
    intro ρ
    have : ρ ∈ MulAction.stabilizer G (t : Finset G) := by rw [hle]; exact Subgroup.mem_top ρ
    exact this

  obtain ⟨σ₀, hσ₀⟩ : (t : Finset G).Nonempty := by
    rw [← Finset.card_pos, t.2]; exact hj0
  have hall : (t : Finset G) = Finset.univ := by
    refine Finset.eq_univ_of_forall fun ρ => ?_
    have hmem : (ρ * σ₀⁻¹) • σ₀ ∈ (ρ * σ₀⁻¹) • (t : Finset G) := Finset.smul_mem_smul_finset hσ₀
    rw [hstab] at hmem
    simpa [mul_smul] using hmem
  have : j = Nat.card G := by
    rw [← t.2, hall, Finset.card_univ, Nat.card_eq_fintype_card]
  omega

omit [Fintype G] in

theorem prod_smul_finset (γ : B) (τ : G) (t : Finset G) :
    ∏ σ ∈ τ • t, σ • γ = τ • ∏ σ ∈ t, σ • γ := by
  rw [← Finset.image_smul, Finset.prod_image (fun a _ b _ h => smul_left_cancel τ h), Finset.smul_prod']
  refine Finset.prod_congr rfl fun σ _ => ?_
  rw [smul_eq_mul, mul_smul]

theorem exists_sum_powersetCard_eq (hℓ : (Nat.card G).Prime) (γ : B) {j : ℕ} (hj0 : 0 < j) (hjℓ : j < Nat.card G) :
    ∃ R : B, (2 ≤ j → R ∈ Ideal.span {x : B | ∃ σ₁ σ₂ : G, σ₁ ≠ σ₂ ∧ x = (σ₁ • γ) * (σ₂ • γ)}) ∧
      ∑ t ∈ Finset.powersetCard j (Finset.univ : Finset G), ∏ σ ∈ t, σ • γ = ∑ τ : G, τ • R := by
  classical
  set I := Ideal.span {x : B | ∃ σ₁ σ₂ : G, σ₁ ≠ σ₂ ∧ x = (σ₁ • γ) * (σ₂ • γ)} with hI

  have hsum : ∑ t ∈ Finset.powersetCard j (Finset.univ : Finset G), ∏ σ ∈ t, σ • γ =
      ∑ t : Sub (G := G) j, ∏ σ ∈ (t : Finset G), σ • γ := by
    rw [← Finset.sum_coe_sort]
    refine Fintype.sum_equiv ((Equiv.subtypeEquivRight fun t => by simp [Finset.mem_powersetCard])) _ _ fun t => rfl
  obtain ⟨R, hR, hRsum⟩ := exists_sum_eq_sum_smul_of_free (B := B) (G := G) (X := Sub (G := G) j)
    (smul_sub_free hℓ hj0 hjℓ) (fun t => ∏ σ ∈ (t : Finset G), σ • γ)
    (fun τ t => by beta_reduce; rw [coe_smul_sub, prod_smul_finset])
    (fun b => 2 ≤ j → b ∈ I) (fun _ => I.zero_mem) (fun a b ha hb h2 => I.add_mem (ha h2) (hb h2))
    (fun t h2 => by
      beta_reduce
      obtain ⟨σ₁, hσ₁⟩ : (t : Finset G).Nonempty := by rw [← Finset.card_pos, t.2]; omega
      obtain ⟨σ₂, hσ₂, hne⟩ : ∃ σ₂ ∈ (t : Finset G), σ₂ ≠ σ₁ := by
        by_contra h
        push Not at h
        have : (t : Finset G) ⊆ {σ₁} := fun x hx => Finset.mem_singleton.2 (h x hx)
        have := Finset.card_le_card this
        rw [t.2, Finset.card_singleton] at this
        omega
      rw [← Finset.mul_prod_erase _ _ hσ₁, ← Finset.mul_prod_erase _ _ (Finset.mem_erase.2 ⟨hne, hσ₂⟩), ← mul_assoc]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨σ₁, σ₂, hne.symm, rfl⟩))
  exact ⟨R, hR, hsum.trans hRsum⟩

end Ws45.CL2
p2m_reactivate "P2MW.S_NumberField_PlaceDecomp_exists_finprod_smul_eq_of_valuation_sub_one_le_of_jump_lt_of_prime_card_decomp.Ws45 P2MW.S_NumberField_PlaceDecomp_exists_finprod_smul_eq_of_valuation_sub_one_le_of_jump_lt_of_prime_card_decomp.Ws45.CL2"
p2m_reactivate "P2MW.S_NumberField_PlaceDecomp_exists_finprod_smul_eq_of_valuation_sub_one_le_of_jump_lt_of_prime_card_decomp.Ws45"

open Ws45.CL2 in
theorem prod_one_add_smul_eq_one_add_finsum_add_finprod_add_finsum_smul_of_prime_card
    {B : Type*} [CommRing B] {G : Type*} [Group G] [Finite G] [MulSemiringAction G B]
    (hℓ : (Nat.card G).Prime) (γ : B) :
    ∃ δ ∈ Ideal.span {x : B | ∃ σ₁ σ₂ : G, σ₁ ≠ σ₂ ∧ x = (σ₁ • γ) * (σ₂ • γ)},
      ∏ᶠ σ : G, (1 + σ • γ) = 1 + ∑ᶠ σ : G, σ • γ + ∏ᶠ σ : G, σ • γ + ∑ᶠ σ : G, σ • δ := by
  classical
  haveI := Fintype.ofFinite G
  set I := Ideal.span {x : B | ∃ σ₁ σ₂ : G, σ₁ ≠ σ₂ ∧ x = (σ₁ • γ) * (σ₂ • γ)} with hI
  set ℓ := Nat.card G with hℓdef
  have hℓ2 : 2 ≤ ℓ := hℓ.two_le
  have hcard : (Finset.univ : Finset G).card = ℓ := by rw [Finset.card_univ, hℓdef, Nat.card_eq_fintype_card]

  have hmid : ∀ j ∈ Finset.Ico 2 ℓ, ∃ R : B, R ∈ I ∧
      ∑ t ∈ Finset.powersetCard j (Finset.univ : Finset G), ∏ σ ∈ t, σ • γ = ∑ τ : G, τ • R := by
    intro j hj
    rw [Finset.mem_Ico] at hj
    obtain ⟨R, hR, hsum⟩ := exists_sum_powersetCard_eq hℓ γ (by omega) hj.2
    exact ⟨R, hR hj.1, hsum⟩
  choose! R hRI hRsum using hmid
  refine ⟨∑ j ∈ Finset.Ico 2 ℓ, R j, I.sum_mem fun j hj => hRI j hj, ?_⟩
  rw [finprod_eq_prod_of_fintype, finsum_eq_sum_of_fintype, finprod_eq_prod_of_fintype, finsum_eq_sum_of_fintype]

  rw [Finset.prod_one_add, Finset.sum_powerset, hcard, Finset.sum_range_succ, Finset.range_eq_Ico,
    ← Finset.sum_Ico_consecutive _ (Nat.zero_le 2) hℓ2]

  have h01 : ∑ j ∈ Finset.Ico 0 2, ∑ t ∈ Finset.powersetCard j (Finset.univ : Finset G), ∏ σ ∈ t, σ • γ =
      1 + ∑ σ : G, σ • γ := by
    rw [show Finset.Ico 0 2 = {0, 1} by decide, Finset.sum_pair (by norm_num), Finset.powersetCard_zero,
      Finset.sum_singleton, Finset.prod_empty, Finset.powersetCard_one, Finset.sum_map]
    simp

  have hℓt : ∑ t ∈ Finset.powersetCard ℓ (Finset.univ : Finset G), ∏ σ ∈ t, σ • γ = ∏ σ : G, σ • γ := by
    rw [← hcard, Finset.powersetCard_self, Finset.sum_singleton]

  have hmidsum : ∑ j ∈ Finset.Ico 2 ℓ, ∑ t ∈ Finset.powersetCard j (Finset.univ : Finset G), ∏ σ ∈ t, σ • γ =
      ∑ τ : G, τ • ∑ j ∈ Finset.Ico 2 ℓ, R j := by
    rw [Finset.sum_congr rfl fun j hj => hRsum j hj, Finset.sum_comm]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Finset.smul_sum]
  rw [h01, hℓt, hmidsum]
  ring

end CL2_inlined
p2m_reactivate "P2MW.S_NumberField_PlaceDecomp_exists_finprod_smul_eq_of_valuation_sub_one_le_of_jump_lt_of_prime_card_decomp.Ws45 P2MW.S_NumberField_PlaceDecomp_exists_finprod_smul_eq_of_valuation_sub_one_le_of_jump_lt_of_prime_card_decomp.Ws45.CL2"

section CL3_inlined

open IsLocalRing Polynomial

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

namespace IsDiscreteValuationRing
p2m_export "IsDiscreteValuationRing" "quotient mk maximalIdeal addVal_eq_zero_of_unit addVal addVal_le_iff_dvd eq_unit_mul_pow_irreducible exists_irreducible addVal_pow addVal_uniformizer not_a_field addVal_eq_top_iff addVal_zero addVal_mul addVal_coe_eq_lowerRamificationCard_zero_mul_addVal_fixedPoints exists_adjoin_singleton_eq_top_of_isSeparable_residueField"
namespace TraceValSol
p2m_open "IsDiscreteValuationRing~mem_maximalIdeal_pow_iff_le_addVal"

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
p2m_reactivate "P2MW.S_NumberField_PlaceDecomp_exists_finprod_smul_eq_of_valuation_sub_one_le_of_jump_lt_of_prime_card_decomp.Ws45 P2MW.S_NumberField_PlaceDecomp_exists_finprod_smul_eq_of_valuation_sub_one_le_of_jump_lt_of_prime_card_decomp.Ws45.CL2"

section action
variable {B : Type*} [CommRing B] {G : Type*} [Group G] [MulSemiringAction G B]
variable {A : Type*} [CommRing A] [Algebra A B] [SMulCommClass G A B]

theorem smul_sub_mem_span_of_adjoin_eq_top {θ : B} (hθ : Algebra.adjoin A {θ} = ⊤) (σ : G) (z : B) :
    σ • z - z ∈ Ideal.span {σ • θ - θ} := by
  have hz : z ∈ Algebra.adjoin A {θ} := hθ ▸ Algebra.mem_top
  induction hz using Algebra.adjoin_induction with
  | mem y hy =>
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact Ideal.subset_span rfl
  | algebraMap a =>
    rw [smul_algebraMap, sub_self]
    exact Ideal.zero_mem _
  | add y w _ _ hy hw =>
    rw [smul_add, add_sub_add_comm]
    exact Ideal.add_mem _ hy hw
  | mul y w _ _ hy hw =>
    have : σ • (y * w) - y * w = (σ • y) * (σ • w - w) + (σ • y - y) * w := by
      rw [smul_mul']
      ring
    rw [this]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hw) (Ideal.mul_mem_right _ _ hy)

theorem smul_eq_self_of_adjoin_eq_top {θ : B} (hθ : Algebra.adjoin A {θ} = ⊤) {σ : G} (hσ : σ • θ = θ)
    (z : B) : σ • z = z := by
  have h := smul_sub_mem_span_of_adjoin_eq_top (A := A) hθ σ z
  rw [hσ, sub_self, Ideal.span_singleton_eq_bot.mpr rfl, Ideal.mem_bot, sub_eq_zero] at h
  exact h

end action
p2m_reactivate "P2MW.S_NumberField_PlaceDecomp_exists_finprod_smul_eq_of_valuation_sub_one_le_of_jump_lt_of_prime_card_decomp.Ws45 P2MW.S_NumberField_PlaceDecomp_exists_finprod_smul_eq_of_valuation_sub_one_le_of_jump_lt_of_prime_card_decomp.Ws45.CL2"

section jump
variable {B : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable {G : Type*} [Group G] [MulSemiringAction G B]
variable {A : Type*} [CommRing A] [Algebra A B] [SMulCommClass G A B]

theorem span_smul_sub_eq_maximalIdeal_pow {θ : B} (hθB : Algebra.adjoin A {θ} = ⊤) (t : ℕ)
    (ht : IsLocalRing.lowerRamificationGroup B G t = ⊤) (ht' : IsLocalRing.lowerRamificationGroup B G (t + 1) = ⊥)
    {σ : G} (hσ : σ ≠ 1) : Ideal.span {σ • θ - θ} = IsLocalRing.maximalIdeal B ^ (t + 1) := by
  apply span_singleton_eq_maximalIdeal_pow_of_addVal_eq
  apply le_antisymm
  · by_contra hlt
    rw [not_le] at hlt
    have hmem : σ • θ - θ ∈ IsLocalRing.maximalIdeal B ^ (t + 1 + 1) := by
      rw [mem_maximalIdeal_pow_iff_le_addVal]
      have hcast : ((t + 1 + 1 : ℕ) : ℕ∞) = ((t + 1 : ℕ) : ℕ∞) + 1 := by push_cast; ring
      rw [hcast]
      exact Order.add_one_le_of_lt hlt
    have hσ' : σ ∈ IsLocalRing.lowerRamificationGroup B G (t + 1) := by
      rw [IsLocalRing.mem_lowerRamificationGroup]
      intro z
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp (smul_sub_mem_span_of_adjoin_eq_top (A := A) hθB σ z)
      rw [hc]
      exact Ideal.mul_mem_right _ _ hmem
    rw [ht'] at hσ'
    exact hσ (Subgroup.mem_bot.mp hσ')
  · rw [← mem_maximalIdeal_pow_iff_le_addVal]
    have hσt : σ ∈ IsLocalRing.lowerRamificationGroup B G t := ht ▸ Subgroup.mem_top σ
    exact (IsLocalRing.mem_lowerRamificationGroup.mp hσt) θ

end jump
p2m_reactivate "P2MW.S_NumberField_PlaceDecomp_exists_finprod_smul_eq_of_valuation_sub_one_le_of_jump_lt_of_prime_card_decomp.Ws45 P2MW.S_NumberField_PlaceDecomp_exists_finprod_smul_eq_of_valuation_sub_one_le_of_jump_lt_of_prime_card_decomp.Ws45.CL2"

section split
variable {A : Type*} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
variable {B : Type*} [CommRing B] [IsDomain B] [Algebra A B] [NoZeroSMulDivisors A B]
variable {G : Type*} [Group G] [Fintype G] [MulSemiringAction G B] [SMulCommClass G A B] [FaithfulSMul G B]
  [Algebra.IsInvariant A B G]

theorem map_minpoly_eq_prod_X_sub_C_smul {θ : B} (hθB : Algebra.adjoin A {θ} = ⊤) (hθint : IsIntegral A θ) :
    (minpoly A θ).map (algebraMap A B) = ∏ σ : G, (X - C (σ • θ)) := by
  classical
  have hinjθ : Function.Injective fun σ : G => σ • θ := by
    intro σ τ hστ
    beta_reduce at hστ
    have h1 : (τ⁻¹ * σ) • θ = θ := by rw [mul_smul, hστ, inv_smul_smul]
    have hall : ∀ z : B, (τ⁻¹ * σ) • z = z := smul_eq_self_of_adjoin_eq_top (A := A) hθB h1
    have h2 : τ⁻¹ * σ = 1 :=
      FaithfulSMul.eq_of_smul_eq_smul (α := B) fun z => by rw [hall z, one_smul]
    exact (inv_mul_eq_one.mp h2).symm
  obtain ⟨p, hpmap, -, hpmonic⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
    (Algebra.IsInvariant.charpoly_mem_lifts A B G θ) (MulSemiringAction.monic_charpoly G θ)
  have h1 : minpoly A θ ∣ p := minpoly.isIntegrallyClosed_dvd hθint (by
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, hpmap, MulSemiringAction.eval_charpoly])
  have h1' : (minpoly A θ).map (algebraMap A B) ∣ ∏ σ : G, (X - C (σ • θ)) := by
    rw [← MulSemiringAction.charpoly_eq, ← hpmap]
    exact Polynomial.map_dvd _ h1
  have hne : (minpoly A θ).map (algebraMap A B) ≠ 0 := ((minpoly.monic hθint).map _).ne_zero
  have h2 : (∏ σ : G, (X - C (σ • θ))) ∣ (minpoly A θ).map (algebraMap A B) := by
    have hroots : ((Finset.univ : Finset G).val.map fun σ => σ • θ) ≤
        ((minpoly A θ).map (algebraMap A B)).roots := by
      rw [Multiset.le_iff_subset (Finset.univ.nodup.map hinjθ)]
      intro a ha
      obtain ⟨σ, -, rfl⟩ := Multiset.mem_map.mp ha
      rw [Polynomial.mem_roots hne, Polynomial.IsRoot.def, Polynomial.eval_map, ← Polynomial.aeval_def]
      exact MulSemiringAction.aeval_smul_minpoly σ θ
    have h3 := (Multiset.prod_X_sub_C_dvd_iff_le_roots hne _).mpr hroots
    rw [Multiset.map_map] at h3
    rw [Finset.prod_eq_multiset_prod]
    exact h3
  exact Polynomial.eq_of_monic_of_associated ((minpoly.monic hθint).map _)
    (Polynomial.monic_prod_of_monic _ _ fun σ _ => Polynomial.monic_X_sub_C _) (associated_of_dvd_dvd h1' h2)

end split
p2m_reactivate "P2MW.S_NumberField_PlaceDecomp_exists_finprod_smul_eq_of_valuation_sub_one_le_of_jump_lt_of_prime_card_decomp.Ws45 P2MW.S_NumberField_PlaceDecomp_exists_finprod_smul_eq_of_valuation_sub_one_le_of_jump_lt_of_prime_card_decomp.Ws45.CL2"

section generates
variable {A K L B : Type*} [CommRing A] [Field K] [CommRing B] [Field L]
variable [Algebra A K] [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L]
variable [IsScalarTower A K L] [IsScalarTower A B L] [IsDomain B] [IsFractionRing B L]

theorem adjoin_algebraMap_eq_top {θ : B} (hθB : Algebra.adjoin A {θ} = ⊤) (hθint : IsIntegral K (algebraMap B L θ)) :
    Algebra.adjoin K {algebraMap B L θ} = ⊤ := by
  apply top_le_iff.mp
  intro l _
  rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hθint.isAlgebraic, IntermediateField.mem_toSubalgebra]
  have hB : ∀ b : B, algebraMap B L b ∈ IntermediateField.adjoin K {algebraMap B L θ} := by
    intro b
    have hb : b ∈ Algebra.adjoin A {θ} := hθB ▸ Algebra.mem_top
    induction hb using Algebra.adjoin_induction with
    | mem y hy =>
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact IntermediateField.mem_adjoin_simple_self K _
    | algebraMap a =>
      rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply A K L]
      exact IntermediateField.algebraMap_mem _ _
    | add y w _ _ hy hw => rw [map_add]; exact add_mem hy hw
    | mul y w _ _ hy hw => rw [map_mul]; exact mul_mem hy hw
  obtain ⟨b, s, -, rfl⟩ := IsFractionRing.div_surjective (A := B) l
  exact div_mem (hB b) (hB s)

end generates
p2m_reactivate "P2MW.S_NumberField_PlaceDecomp_exists_finprod_smul_eq_of_valuation_sub_one_le_of_jump_lt_of_prime_card_decomp.Ws45 P2MW.S_NumberField_PlaceDecomp_exists_finprod_smul_eq_of_valuation_sub_one_le_of_jump_lt_of_prime_card_decomp.Ws45.CL2"

section trace
variable {A K L B : Type*} [CommRing A] [Field K] [CommRing B] [Field L]
variable [Algebra A K] [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L]
variable [IsScalarTower A K L] [IsScalarTower A B L]
variable [IsDomain A] [IsFractionRing A K] [FiniteDimensional K L] [Algebra.IsSeparable K L]
variable [IsIntegralClosure B A L] [IsIntegrallyClosed A] [IsDomain B] [IsDiscreteValuationRing B]
variable [IsFractionRing B L] [Module.IsTorsionFree A B]

theorem exists_trace_eq_mul {d e : ℕ} (hdiff : differentIdeal A B = IsLocalRing.maximalIdeal B ^ d)
    {ϖ : A} (hϖB : Ideal.span {algebraMap A B ϖ} = IsLocalRing.maximalIdeal B ^ e)
    {m : ℕ} {x : B} (hx : x ∈ IsLocalRing.maximalIdeal B ^ m) :
    ∃ c : A, Algebra.trace K L (algebraMap B L x) = algebraMap A K (ϖ ^ ((m + d) / e) * c) := by
  classical
  set r := (m + d) / e with hr
  have hrle : e * r ≤ m + d := by rw [mul_comm]; exact Nat.div_mul_le_self _ _
  have hϖ0 : algebraMap A B ϖ ≠ 0 := by
    intro h0
    rw [h0, Ideal.span_singleton_eq_bot.mpr rfl] at hϖB
    exact pow_ne_zero _ (IsDiscreteValuationRing.not_a_field B) hϖB.symm
  have hϖL : algebraMap A L ϖ ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply A B L]
    exact fun h0 => hϖ0 ((IsFractionRing.to_map_eq_zero_iff (K := L)).mp h0)
  have h𝔡0 : ((differentIdeal A B : Ideal B) : FractionalIdeal (nonZeroDivisors B) L) ≠ 0 := by
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero, hdiff]
    exact pow_ne_zero _ (IsDiscreteValuationRing.not_a_field B)
  set z : L := algebraMap B L x * ((algebraMap A L ϖ)⁻¹) ^ r with hz_def
  have hz : z ∈ FractionalIdeal.dual A K (1 : FractionalIdeal (nonZeroDivisors B) L) := by
    have hdual : FractionalIdeal.dual A K (1 : FractionalIdeal (nonZeroDivisors B) L) =
        ((differentIdeal A B : Ideal B) : FractionalIdeal (nonZeroDivisors B) L)⁻¹ := by
      rw [coeIdeal_differentIdeal A K L B, inv_inv]
    rw [hdual, FractionalIdeal.mem_inv_iff h𝔡0]
    intro w hw
    obtain ⟨w', hw', rfl⟩ := (FractionalIdeal.mem_coeIdeal _).mp hw
    rw [hdiff] at hw'
    have hxw : x * w' ∈ IsLocalRing.maximalIdeal B ^ (e * r) :=
      Ideal.pow_le_pow_right hrle (by rw [pow_add]; exact Ideal.mul_mem_mul hx hw')
    rw [pow_mul, ← hϖB, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hxw
    obtain ⟨b, hb⟩ := hxw
    rw [FractionalIdeal.mem_one_iff]
    refine ⟨b, ?_⟩
    have hmap : algebraMap B L (x * w') = algebraMap A L ϖ ^ r * algebraMap B L b := by
      rw [hb, map_mul, map_pow, ← IsScalarTower.algebraMap_apply A B L]
    rw [map_mul] at hmap
    rw [hz_def, mul_right_comm, hmap, inv_pow, mul_assoc, mul_comm (algebraMap B L b), ← mul_assoc,
      mul_inv_cancel₀ (pow_ne_zero r hϖL), one_mul]
  have h10 : (1 : FractionalIdeal (nonZeroDivisors B) L) ≠ 0 := one_ne_zero
  obtain ⟨c, hc⟩ := (FractionalIdeal.mem_dual h10).mp hz 1
    ((FractionalIdeal.mem_one_iff _).mpr ⟨1, map_one _⟩)
  rw [Algebra.traceForm_apply, mul_one] at hc
  refine ⟨c, ?_⟩
  have hxz : algebraMap B L x = (algebraMap A K ϖ) ^ r • z := by
    rw [hz_def, Algebra.smul_def, map_pow, ← IsScalarTower.algebraMap_apply A K L, inv_pow,
      ← mul_assoc, mul_comm _ (algebraMap B L x), mul_assoc, mul_inv_cancel₀ (pow_ne_zero r hϖL), mul_one]
  rw [RingHom.map_mul, RingHom.map_pow, hc, hxz, LinearMap.map_smul, smul_eq_mul]

end trace
p2m_reactivate "P2MW.S_NumberField_PlaceDecomp_exists_finprod_smul_eq_of_valuation_sub_one_le_of_jump_lt_of_prime_card_decomp.Ws45 P2MW.S_NumberField_PlaceDecomp_exists_finprod_smul_eq_of_valuation_sub_one_le_of_jump_lt_of_prime_card_decomp.Ws45.CL2"

section galsum

theorem finsum_smul_eq_algebraMap_trace (K L : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G L] [IsGaloisGroup G K L] (y : L) :
    ∑ᶠ σ : G, σ • y = algebraMap K L (Algebra.trace K L y) := by
  classical
  haveI := Fintype.ofFinite G
  rw [finsum_eq_sum_of_fintype, trace_eq_sum_automorphisms,
    ← Fintype.sum_equiv (IsGaloisGroup.mulEquivAlgEquiv G K L).toEquiv (fun σ : G => σ • y) (fun τ : (L ≃ₐ[K] L) => τ y)]
  intro σ
  simp [IsGaloisGroup.mulEquivAlgEquiv]
end galsum
p2m_reactivate "P2MW.S_NumberField_PlaceDecomp_exists_finprod_smul_eq_of_valuation_sub_one_le_of_jump_lt_of_prime_card_decomp.Ws45 P2MW.S_NumberField_PlaceDecomp_exists_finprod_smul_eq_of_valuation_sub_one_le_of_jump_lt_of_prime_card_decomp.Ws45.CL2"

end IsDiscreteValuationRing.TraceValSol
p2m_reactivate "P2MW.S_NumberField_PlaceDecomp_exists_finprod_smul_eq_of_valuation_sub_one_le_of_jump_lt_of_prime_card_decomp.Ws45 P2MW.S_NumberField_PlaceDecomp_exists_finprod_smul_eq_of_valuation_sub_one_le_of_jump_lt_of_prime_card_decomp.Ws45.CL2"
p2m_reactivate "P2MW.S_NumberField_PlaceDecomp_exists_finprod_smul_eq_of_valuation_sub_one_le_of_jump_lt_of_prime_card_decomp.Ws45 P2MW.S_NumberField_PlaceDecomp_exists_finprod_smul_eq_of_valuation_sub_one_le_of_jump_lt_of_prime_card_decomp.Ws45.CL2"

namespace IsDiscreteValuationRing p2m_export "IsDiscreteValuationRing" "quotient mk maximalIdeal addVal_eq_zero_of_unit addVal addVal_le_iff_dvd eq_unit_mul_pow_irreducible exists_irreducible addVal_pow addVal_uniformizer not_a_field addVal_eq_top_iff addVal_zero addVal_mul addVal_coe_eq_lowerRamificationCard_zero_mul_addVal_fixedPoints exists_adjoin_singleton_eq_top_of_isSeparable_residueField" end IsDiscreteValuationRing
p2m_open_scoped "IsDiscreteValuationRing" in
open IsDiscreteValuationRing.TraceValSol in

set_option maxHeartbeats 3200000 in
theorem IsDiscreteValuationRing.finsum_smul_mem_maximalIdeal_pow_of_lowerRamificationGroup_eq_top_of_eq_bot
    {B : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G B] [FaithfulSMul G B]
    [(IsLocalRing.maximalIdeal B).LiesOver (IsLocalRing.maximalIdeal (FixedPoints.subring B G))]
    [Algebra.IsSeparable
      (FixedPoints.subring B G ⧸ IsLocalRing.maximalIdeal (FixedPoints.subring B G))
      (B ⧸ IsLocalRing.maximalIdeal B)]
    (t : ℕ) (ht : IsLocalRing.lowerRamificationGroup B G t = ⊤)
    (ht' : IsLocalRing.lowerRamificationGroup B G (t + 1) = ⊥)
    (m : ℕ) (x : B) (hx : x ∈ IsLocalRing.maximalIdeal B ^ m) :
    ∑ᶠ σ : G, σ • x ∈
      IsLocalRing.maximalIdeal B ^ (Nat.card G * ((m + (t + 1) * (Nat.card G - 1)) / Nat.card G)) := by
  classical

  let A := FixedPoints.subring B G
  let K := FractionRing A
  let L := FractionRing B
  haveI : IsDiscreteValuationRing A := FixedPoints.isDiscreteValuationRing_subring
  haveI hGAB : IsGaloisGroup G A B := FixedPoints.isGaloisGroup_subring
  haveI : SMulCommClass G A B := hGAB.commutes
  haveI : Algebra.IsInvariant A B G := hGAB.isInvariant
  haveI : NoZeroSMulDivisors A B :=
    ⟨fun {a y} h => by
      rcases mul_eq_zero.mp (show (a : B) * y = 0 from h) with ha | hy
      · exact Or.inl (Subtype.ext ha)
      · exact Or.inr hy⟩
  letI := IsFractionRing.mulSemiringAction G B L
  haveI : SMulDistribClass G B L := IsFractionRing.smulDistribClass G B L
  haveI hGal : IsGaloisGroup G K L := IsGaloisGroup.toFractionRing G A B
  haveI := IsGaloisGroup.finiteDimensional G K L
  haveI := IsGaloisGroup.isGalois G K L
  haveI : Algebra.IsIntegral A B := Algebra.IsInvariant.isIntegral A B G
  haveI : Module.Finite A B := IsIntegralClosure.finite A K L B
  haveI : Fintype G := Fintype.ofFinite G

  have hG0 : IsLocalRing.lowerRamificationGroup B G 0 = ⊤ :=
    top_le_iff.mp (ht ▸ IsLocalRing.lowerRamificationGroup_antitone (Nat.zero_le t))
  have hcard0 : IsLocalRing.lowerRamificationCard B G 0 = Nat.card G := by
    rw [IsLocalRing.lowerRamificationCard, hG0, Subgroup.card_top]
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hval : IsDiscreteValuationRing.addVal B (ϖ : B) = (Nat.card G : ℕ∞) := by
    rw [IsDiscreteValuationRing.addVal_coe_eq_lowerRamificationCard_zero_mul_addVal_fixedPoints ϖ, hcard0,
      IsDiscreteValuationRing.addVal_uniformizer hϖ, mul_one]
  have hϖB : Ideal.span {algebraMap A B ϖ} = IsLocalRing.maximalIdeal B ^ Nat.card G :=
    span_singleton_eq_maximalIdeal_pow_of_addVal_eq hval

  haveI hlocG : IsLocalHom (algebraMap A B) :=
    ⟨fun a h => (FixedPoints.isUnit_subring_iff a).mpr h⟩
  haveI : Algebra.IsSeparable (ResidueField A) (ResidueField B) :=
    (inferInstance : Algebra.IsSeparable
      (FixedPoints.subring B G ⧸ IsLocalRing.maximalIdeal (FixedPoints.subring B G))
      (B ⧸ IsLocalRing.maximalIdeal B))
  obtain ⟨θ, hθB⟩ := IsDiscreteValuationRing.exists_adjoin_singleton_eq_top_of_isSeparable_residueField
    (A := A) (B := B) Subtype.coe_injective
  have hθint : IsIntegral A θ := Algebra.IsIntegral.isIntegral θ

  have hsplit : (minpoly A θ).map (algebraMap A B) = ∏ σ : G, (X - C (σ • θ)) :=
    map_minpoly_eq_prod_X_sub_C_smul hθB hθint
  have hθL : Algebra.adjoin K {algebraMap B L θ} = ⊤ :=
    adjoin_algebraMap_eq_top hθB (hθint.algebraMap (B := L)).tower_top
  have hdiff : differentIdeal A B = ∏ σ ∈ Finset.univ.erase (1 : G), Ideal.span {σ • θ - θ} :=
    differentIdeal_eq_prod_span_smul_sub A K L B G θ hθL hθB hsplit
  have hdiff' : differentIdeal A B = IsLocalRing.maximalIdeal B ^ ((t + 1) * (Nat.card G - 1)) := by
    rw [hdiff, Finset.prod_congr rfl fun σ hσ =>
      span_smul_sub_eq_maximalIdeal_pow (A := A) hθB t ht ht' (Finset.ne_of_mem_erase hσ),
      Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ← pow_mul,
      Nat.card_eq_fintype_card]

  obtain ⟨c, hc⟩ := exists_trace_eq_mul (K := K) (L := L) hdiff' hϖB hx
  have hsum : algebraMap B L (∑ σ : G, σ • x) = algebraMap K L (Algebra.trace K L (algebraMap B L x)) := by
    rw [← finsum_smul_eq_algebraMap_trace K L G, finsum_eq_sum_of_fintype, map_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    exact algebraMap.smul' σ x L
  have hfinal : algebraMap B L (∑ σ : G, σ • x) =
      algebraMap B L (algebraMap A B (ϖ ^ ((m + (t + 1) * (Nat.card G - 1)) / Nat.card G) * c)) := by
    rw [hsum, ← IsScalarTower.algebraMap_apply A B L, IsScalarTower.algebraMap_apply A K L, hc]
  have hEq := IsFractionRing.injective B L hfinal
  rw [finsum_eq_sum_of_fintype, hEq, pow_mul, ← hϖB, Ideal.span_singleton_pow, map_mul, map_pow]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

end CL3_inlined
p2m_reactivate "P2MW.S_NumberField_PlaceDecomp_exists_finprod_smul_eq_of_valuation_sub_one_le_of_jump_lt_of_prime_card_decomp.Ws45 P2MW.S_NumberField_PlaceDecomp_exists_finprod_smul_eq_of_valuation_sub_one_le_of_jump_lt_of_prime_card_decomp.Ws45.CL2"

section S1_inlined

open IsLocalRing Polynomial

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

namespace IsDiscreteValuationRing
p2m_export "IsDiscreteValuationRing" "quotient mk maximalIdeal addVal_eq_zero_of_unit addVal addVal_le_iff_dvd eq_unit_mul_pow_irreducible exists_irreducible addVal_pow addVal_uniformizer not_a_field addVal_eq_top_iff addVal_zero addVal_mul addVal_coe_eq_lowerRamificationCard_zero_mul_addVal_fixedPoints exists_adjoin_singleton_eq_top_of_isSeparable_residueField"
namespace TraceOntoSol
p2m_open "IsDiscreteValuationRing~mem_maximalIdeal_pow_iff_le_addVal"

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
p2m_reactivate "P2MW.S_NumberField_PlaceDecomp_exists_finprod_smul_eq_of_valuation_sub_one_le_of_jump_lt_of_prime_card_decomp.Ws45 P2MW.S_NumberField_PlaceDecomp_exists_finprod_smul_eq_of_valuation_sub_one_le_of_jump_lt_of_prime_card_decomp.Ws45.CL2"

section action
variable {B : Type*} [CommRing B] {G : Type*} [Group G] [MulSemiringAction G B]
variable {A : Type*} [CommRing A] [Algebra A B] [SMulCommClass G A B]

theorem smul_sub_mem_span_of_adjoin_eq_top {θ : B} (hθ : Algebra.adjoin A {θ} = ⊤) (σ : G) (z : B) :
    σ • z - z ∈ Ideal.span {σ • θ - θ} := by
  have hz : z ∈ Algebra.adjoin A {θ} := hθ ▸ Algebra.mem_top
  induction hz using Algebra.adjoin_induction with
  | mem y hy =>
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact Ideal.subset_span rfl
  | algebraMap a =>
    rw [smul_algebraMap, sub_self]
    exact Ideal.zero_mem _
  | add y w _ _ hy hw =>
    rw [smul_add, add_sub_add_comm]
    exact Ideal.add_mem _ hy hw
  | mul y w _ _ hy hw =>
    have : σ • (y * w) - y * w = (σ • y) * (σ • w - w) + (σ • y - y) * w := by
      rw [smul_mul']
      ring
    rw [this]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hw) (Ideal.mul_mem_right _ _ hy)

theorem smul_eq_self_of_adjoin_eq_top {θ : B} (hθ : Algebra.adjoin A {θ} = ⊤) {σ : G} (hσ : σ • θ = θ)
    (z : B) : σ • z = z := by
  have h := smul_sub_mem_span_of_adjoin_eq_top (A := A) hθ σ z
  rw [hσ, sub_self, Ideal.span_singleton_eq_bot.mpr rfl, Ideal.mem_bot, sub_eq_zero] at h
  exact h

end action
p2m_reactivate "P2MW.S_NumberField_PlaceDecomp_exists_finprod_smul_eq_of_valuation_sub_one_le_of_jump_lt_of_prime_card_decomp.Ws45 P2MW.S_NumberField_PlaceDecomp_exists_finprod_smul_eq_of_valuation_sub_one_le_of_jump_lt_of_prime_card_decomp.Ws45.CL2"

section jump
variable {B : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable {G : Type*} [Group G] [MulSemiringAction G B]
variable {A : Type*} [CommRing A] [Algebra A B] [SMulCommClass G A B]

theorem span_smul_sub_eq_maximalIdeal_pow {θ : B} (hθB : Algebra.adjoin A {θ} = ⊤) (t : ℕ)
    (ht : IsLocalRing.lowerRamificationGroup B G t = ⊤) (ht' : IsLocalRing.lowerRamificationGroup B G (t + 1) = ⊥)
    {σ : G} (hσ : σ ≠ 1) : Ideal.span {σ • θ - θ} = IsLocalRing.maximalIdeal B ^ (t + 1) := by
  apply span_singleton_eq_maximalIdeal_pow_of_addVal_eq
  apply le_antisymm
  · by_contra hlt
    rw [not_le] at hlt
    have hmem : σ • θ - θ ∈ IsLocalRing.maximalIdeal B ^ (t + 1 + 1) := by
      rw [mem_maximalIdeal_pow_iff_le_addVal]
      have hcast : ((t + 1 + 1 : ℕ) : ℕ∞) = ((t + 1 : ℕ) : ℕ∞) + 1 := by push_cast; ring
      rw [hcast]
      exact Order.add_one_le_of_lt hlt
    have hσ' : σ ∈ IsLocalRing.lowerRamificationGroup B G (t + 1) := by
      rw [IsLocalRing.mem_lowerRamificationGroup]
      intro z
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp (smul_sub_mem_span_of_adjoin_eq_top (A := A) hθB σ z)
      rw [hc]
      exact Ideal.mul_mem_right _ _ hmem
    rw [ht'] at hσ'
    exact hσ (Subgroup.mem_bot.mp hσ')
  · rw [← mem_maximalIdeal_pow_iff_le_addVal]
    have hσt : σ ∈ IsLocalRing.lowerRamificationGroup B G t := ht ▸ Subgroup.mem_top σ
    exact (IsLocalRing.mem_lowerRamificationGroup.mp hσt) θ

end jump
p2m_reactivate "P2MW.S_NumberField_PlaceDecomp_exists_finprod_smul_eq_of_valuation_sub_one_le_of_jump_lt_of_prime_card_decomp.Ws45 P2MW.S_NumberField_PlaceDecomp_exists_finprod_smul_eq_of_valuation_sub_one_le_of_jump_lt_of_prime_card_decomp.Ws45.CL2"

section split
variable {A : Type*} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
variable {B : Type*} [CommRing B] [IsDomain B] [Algebra A B] [NoZeroSMulDivisors A B]
variable {G : Type*} [Group G] [Fintype G] [MulSemiringAction G B] [SMulCommClass G A B] [FaithfulSMul G B]
  [Algebra.IsInvariant A B G]

theorem map_minpoly_eq_prod_X_sub_C_smul {θ : B} (hθB : Algebra.adjoin A {θ} = ⊤) (hθint : IsIntegral A θ) :
    (minpoly A θ).map (algebraMap A B) = ∏ σ : G, (X - C (σ • θ)) := by
  classical
  have hinjθ : Function.Injective fun σ : G => σ • θ := by
    intro σ τ hστ
    beta_reduce at hστ
    have h1 : (τ⁻¹ * σ) • θ = θ := by rw [mul_smul, hστ, inv_smul_smul]
    have hall : ∀ z : B, (τ⁻¹ * σ) • z = z := smul_eq_self_of_adjoin_eq_top (A := A) hθB h1
    have h2 : τ⁻¹ * σ = 1 :=
      FaithfulSMul.eq_of_smul_eq_smul (α := B) fun z => by rw [hall z, one_smul]
    exact (inv_mul_eq_one.mp h2).symm
  obtain ⟨p, hpmap, -, hpmonic⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
    (Algebra.IsInvariant.charpoly_mem_lifts A B G θ) (MulSemiringAction.monic_charpoly G θ)
  have h1 : minpoly A θ ∣ p := minpoly.isIntegrallyClosed_dvd hθint (by
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, hpmap, MulSemiringAction.eval_charpoly])
  have h1' : (minpoly A θ).map (algebraMap A B) ∣ ∏ σ : G, (X - C (σ • θ)) := by
    rw [← MulSemiringAction.charpoly_eq, ← hpmap]
    exact Polynomial.map_dvd _ h1
  have hne : (minpoly A θ).map (algebraMap A B) ≠ 0 := ((minpoly.monic hθint).map _).ne_zero
  have h2 : (∏ σ : G, (X - C (σ • θ))) ∣ (minpoly A θ).map (algebraMap A B) := by
    have hroots : ((Finset.univ : Finset G).val.map fun σ => σ • θ) ≤
        ((minpoly A θ).map (algebraMap A B)).roots := by
      rw [Multiset.le_iff_subset (Finset.univ.nodup.map hinjθ)]
      intro a ha
      obtain ⟨σ, -, rfl⟩ := Multiset.mem_map.mp ha
      rw [Polynomial.mem_roots hne, Polynomial.IsRoot.def, Polynomial.eval_map, ← Polynomial.aeval_def]
      exact MulSemiringAction.aeval_smul_minpoly σ θ
    have h3 := (Multiset.prod_X_sub_C_dvd_iff_le_roots hne _).mpr hroots
    rw [Multiset.map_map] at h3
    rw [Finset.prod_eq_multiset_prod]
    exact h3
  exact Polynomial.eq_of_monic_of_associated ((minpoly.monic hθint).map _)
    (Polynomial.monic_prod_of_monic _ _ fun σ _ => Polynomial.monic_X_sub_C _) (associated_of_dvd_dvd h1' h2)

end split
p2m_reactivate "P2MW.S_NumberField_PlaceDecomp_exists_finprod_smul_eq_of_valuation_sub_one_le_of_jump_lt_of_prime_card_decomp.Ws45 P2MW.S_NumberField_PlaceDecomp_exists_finprod_smul_eq_of_valuation_sub_one_le_of_jump_lt_of_prime_card_decomp.Ws45.CL2"

section generates
variable {A K L B : Type*} [CommRing A] [Field K] [CommRing B] [Field L]
variable [Algebra A K] [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L]
variable [IsScalarTower A K L] [IsScalarTower A B L] [IsDomain B] [IsFractionRing B L]

theorem adjoin_algebraMap_eq_top {θ : B} (hθB : Algebra.adjoin A {θ} = ⊤) (hθint : IsIntegral K (algebraMap B L θ)) :
    Algebra.adjoin K {algebraMap B L θ} = ⊤ := by
  apply top_le_iff.mp
  intro l _
  rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hθint.isAlgebraic, IntermediateField.mem_toSubalgebra]
  have hB : ∀ b : B, algebraMap B L b ∈ IntermediateField.adjoin K {algebraMap B L θ} := by
    intro b
    have hb : b ∈ Algebra.adjoin A {θ} := hθB ▸ Algebra.mem_top
    induction hb using Algebra.adjoin_induction with
    | mem y hy =>
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact IntermediateField.mem_adjoin_simple_self K _
    | algebraMap a =>
      rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply A K L]
      exact IntermediateField.algebraMap_mem _ _
    | add y w _ _ hy hw => rw [map_add]; exact add_mem hy hw
    | mul y w _ _ hy hw => rw [map_mul]; exact mul_mem hy hw
  obtain ⟨b, s, -, rfl⟩ := IsFractionRing.div_surjective (A := B) l
  exact div_mem (hB b) (hB s)

end generates
p2m_reactivate "P2MW.S_NumberField_PlaceDecomp_exists_finprod_smul_eq_of_valuation_sub_one_le_of_jump_lt_of_prime_card_decomp.Ws45 P2MW.S_NumberField_PlaceDecomp_exists_finprod_smul_eq_of_valuation_sub_one_le_of_jump_lt_of_prime_card_decomp.Ws45.CL2"

section trace
variable {A K L B : Type*} [CommRing A] [Field K] [CommRing B] [Field L]
variable [Algebra A K] [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L]
variable [IsScalarTower A K L] [IsScalarTower A B L]
variable [IsDomain A] [IsDiscreteValuationRing A] [IsFractionRing A K] [FiniteDimensional K L] [Algebra.IsSeparable K L]
variable [IsIntegralClosure B A L] [IsDomain B] [IsDiscreteValuationRing B]
variable [IsFractionRing B L] [Module.IsTorsionFree A B]

theorem exists_algebraMap_eq_trace (y : B) : ∃ a : A, algebraMap A K a = Algebra.trace K L (algebraMap B L y) := by
  have hint : IsIntegral A (Algebra.trace K L (algebraMap B L y)) :=
    Algebra.isIntegral_trace ((IsIntegralClosure.isIntegral A L y).algebraMap)
  exact IsIntegrallyClosed.isIntegral_iff.mp hint

theorem trace_algebraMap_mul (a : A) (y : B) :
    Algebra.trace K L (algebraMap B L (algebraMap A B a * y)) = algebraMap A K a * Algebra.trace K L (algebraMap B L y) := by
  rw [map_mul, ← IsScalarTower.algebraMap_apply A B L, IsScalarTower.algebraMap_apply A K L, ← Algebra.smul_def,
    LinearMap.map_smul, smul_eq_mul]

theorem exists_mem_pow_and_trace_eq {d e : ℕ} (hdiff : differentIdeal A B = IsLocalRing.maximalIdeal B ^ d)
    {ϖ : A} (hϖ : Irreducible ϖ) (hϖB : Ideal.span {algebraMap A B ϖ} = IsLocalRing.maximalIdeal B ^ e) (he : 0 < e)
    (m : ℕ) (c : A) :
    ∃ y : B, y ∈ IsLocalRing.maximalIdeal B ^ m ∧
      Algebra.trace K L (algebraMap B L y) = algebraMap A K (ϖ ^ ((m + d) / e) * c) := by
  classical
  set r := (m + d) / e with hr
  have hϖ0 : algebraMap A B ϖ ≠ 0 := by
    intro h0
    rw [h0, Ideal.span_singleton_eq_bot.mpr rfl] at hϖB
    exact pow_ne_zero _ (IsDiscreteValuationRing.not_a_field B) hϖB.symm
  have hinjK : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
  have hϖK : algebraMap A K ϖ ≠ 0 := fun h0 => hϖ.ne_zero (hinjK (h0.trans (map_zero _).symm))
  have hϖL : algebraMap A L ϖ ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply A B L]
    exact fun h0 => hϖ0 ((IsFractionRing.to_map_eq_zero_iff (K := L)).mp h0)
  have hϖmem : algebraMap A B ϖ ∈ IsLocalRing.maximalIdeal B := by
    have h1 : algebraMap A B ϖ ∈ Ideal.span {algebraMap A B ϖ} := Ideal.mem_span_singleton_self _
    rw [hϖB] at h1
    exact Ideal.pow_le_self he.ne' h1

  have htr0 : ∃ y ∈ IsLocalRing.maximalIdeal B ^ m, Algebra.trace K L (algebraMap B L y) ≠ 0 := by
    obtain ⟨l, hl⟩ := Algebra.trace_surjective K L 1
    obtain ⟨a, ha0, hal⟩ := exists_integral_multiples A K ({l} : Finset L)
    obtain ⟨b, hb⟩ := (IsIntegralClosure.isIntegral_iff (A := B)).mp (hal l (Finset.mem_singleton_self l))
    refine ⟨algebraMap A B (ϖ ^ m * a) * b, ?_, ?_⟩
    · rw [map_mul]
      exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (by rw [map_pow]; exact Ideal.pow_mem_pow hϖmem m))
    · rw [trace_algebraMap_mul, hb, ← algebraMap_smul K a l, LinearMap.map_smul, hl, smul_eq_mul, mul_one, ← map_mul]
      exact fun h0 => (mul_ne_zero (mul_ne_zero (pow_ne_zero m hϖ.ne_zero) ha0) ha0)
        (hinjK (h0.trans (map_zero _).symm))

  have hP : ∃ j : ℕ, ∃ y ∈ IsLocalRing.maximalIdeal B ^ m, ∃ a : A, a ≠ 0 ∧
      algebraMap A K a = Algebra.trace K L (algebraMap B L y) ∧ IsDiscreteValuationRing.addVal A a = j := by
    obtain ⟨y, hy, hy0⟩ := htr0
    obtain ⟨a, ha⟩ := exists_algebraMap_eq_trace (A := A) (K := K) (L := L) y
    have ha0 : a ≠ 0 := fun h0 => hy0 (by rw [← ha, h0, map_zero])
    obtain ⟨j, hj⟩ := WithTop.ne_top_iff_exists.mp
      (fun h => ha0 (IsDiscreteValuationRing.addVal_eq_top_iff.mp h))
    exact ⟨j, y, hy, a, ha0, ha, hj.symm⟩
  obtain ⟨y₀, hy₀, a₀, ha₀0, ha₀, hj⟩ := Nat.find_spec hP
  have hmin : ∀ z ∈ IsLocalRing.maximalIdeal B ^ m, ∃ a' : A,
      algebraMap A K (ϖ ^ Nat.find hP * a') = Algebra.trace K L (algebraMap B L z) := by
    intro z hz
    obtain ⟨a, ha⟩ := exists_algebraMap_eq_trace (A := A) (K := K) (L := L) z
    by_cases ha0 : a = 0
    · exact ⟨0, by rw [mul_zero, map_zero, ← ha, ha0, map_zero]⟩
    obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp
      (fun h => ha0 (IsDiscreteValuationRing.addVal_eq_top_iff.mp h))
    have hjk : Nat.find hP ≤ k := Nat.find_min' hP ⟨z, hz, a, ha0, ha, hk.symm⟩
    have hdvd : ϖ ^ Nat.find hP ∣ a := by
      rw [← IsDiscreteValuationRing.addVal_le_iff_dvd, IsDiscreteValuationRing.addVal_pow,
        IsDiscreteValuationRing.addVal_uniformizer hϖ, nsmul_one, ← hk]
      exact Nat.cast_le.mpr hjk
    obtain ⟨a', rfl⟩ := hdvd
    exact ⟨a', ha⟩
  set j := Nat.find hP with hjdef

  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible B
  have hπmem : π ∈ IsLocalRing.maximalIdeal B := by
    rw [hπ.maximalIdeal_eq]; exact Ideal.mem_span_singleton_self π
  have hπm : π ^ m ∈ IsLocalRing.maximalIdeal B ^ m := Ideal.pow_mem_pow hπmem m
  have hπd : π ^ d ∈ IsLocalRing.maximalIdeal B ^ d := Ideal.pow_mem_pow hπmem d
  set z : L := algebraMap B L (π ^ m) * ((algebraMap A L ϖ)⁻¹) ^ j with hz_def
  have hz : z ∈ FractionalIdeal.dual A K (1 : FractionalIdeal (nonZeroDivisors B) L) := by
    have h10 : (1 : FractionalIdeal (nonZeroDivisors B) L) ≠ 0 := one_ne_zero
    rw [FractionalIdeal.mem_dual h10]
    intro w hw
    obtain ⟨b, rfl⟩ := (FractionalIdeal.mem_one_iff _).mp hw
    obtain ⟨a', ha'⟩ := hmin (π ^ m * b) (Ideal.mul_mem_right _ _ hπm)
    refine ⟨a', ?_⟩
    have hzb : z * algebraMap B L b = ((algebraMap A K ϖ)⁻¹ ^ j) • algebraMap B L (π ^ m * b) := by
      rw [hz_def, Algebra.smul_def, map_pow (algebraMap K L), map_inv₀, ← IsScalarTower.algebraMap_apply A K L, map_mul]
      ring
    rw [Algebra.traceForm_apply, hzb, LinearMap.map_smul, smul_eq_mul, ← ha', map_mul, map_pow, inv_pow,
      ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero j hϖK), one_mul]
  have h𝔡0 : ((differentIdeal A B : Ideal B) : FractionalIdeal (nonZeroDivisors B) L) ≠ 0 := by
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero, hdiff]
    exact pow_ne_zero _ (IsDiscreteValuationRing.not_a_field B)
  have hdual : FractionalIdeal.dual A K (1 : FractionalIdeal (nonZeroDivisors B) L) =
      ((differentIdeal A B : Ideal B) : FractionalIdeal (nonZeroDivisors B) L)⁻¹ := by
    rw [coeIdeal_differentIdeal A K L B, inv_inv]
  rw [hdual, FractionalIdeal.mem_inv_iff h𝔡0] at hz
  have hw : algebraMap B L (π ^ d) ∈ ((differentIdeal A B : Ideal B) : FractionalIdeal (nonZeroDivisors B) L) :=
    (FractionalIdeal.mem_coeIdeal _).mpr ⟨π ^ d, by rw [hdiff]; exact hπd, rfl⟩
  obtain ⟨b', hb'⟩ := (FractionalIdeal.mem_one_iff _).mp (hz _ hw)
  have hEq : algebraMap B L (π ^ (m + d)) = algebraMap B L (algebraMap A B ϖ ^ j * b') := by
    rw [map_mul, hb', hz_def, pow_add, map_mul, map_pow (algebraMap B L) (algebraMap A B ϖ),
      ← IsScalarTower.algebraMap_apply A B L, inv_pow, mul_right_comm (algebraMap B L (π ^ m)),
      mul_comm ((algebraMap A L ϖ) ^ j), inv_mul_cancel_right₀ (pow_ne_zero j hϖL)]
  have hπmd : π ^ (m + d) ∈ IsLocalRing.maximalIdeal B ^ (e * j) := by
    rw [pow_mul, ← hϖB, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact ⟨b', IsFractionRing.injective B L hEq⟩
  rw [mem_maximalIdeal_pow_iff_le_addVal, IsDiscreteValuationRing.addVal_pow,
    IsDiscreteValuationRing.addVal_uniformizer hπ, nsmul_one] at hπmd
  have hej : e * j ≤ m + d := by exact_mod_cast hπmd
  have hjr : j ≤ r := (Nat.le_div_iff_mul_le he).mpr (by rwa [mul_comm] at hej)

  obtain ⟨k, u, hk⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha₀0 hϖ
  have hkj : k = j := by
    have h := hj
    rw [hk, IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_pow,
      IsDiscreteValuationRing.addVal_uniformizer hϖ, nsmul_one, IsDiscreteValuationRing.addVal_eq_zero_of_unit,
      zero_add] at h
    exact_mod_cast h
  refine ⟨algebraMap A B ((↑u⁻¹ : A) * ϖ ^ (r - j) * c) * y₀, Ideal.mul_mem_left _ _ hy₀, ?_⟩
  rw [trace_algebraMap_mul, ← ha₀, ← map_mul, hk, hkj]
  congr 1
  rw [show (↑u⁻¹ : A) * ϖ ^ (r - j) * c * (↑u * ϖ ^ j) = (↑u⁻¹ * ↑u) * (ϖ ^ (r - j) * ϖ ^ j) * c by ring,
    Units.inv_mul, one_mul, ← pow_add, Nat.sub_add_cancel hjr]

end trace
p2m_reactivate "P2MW.S_NumberField_PlaceDecomp_exists_finprod_smul_eq_of_valuation_sub_one_le_of_jump_lt_of_prime_card_decomp.Ws45 P2MW.S_NumberField_PlaceDecomp_exists_finprod_smul_eq_of_valuation_sub_one_le_of_jump_lt_of_prime_card_decomp.Ws45.CL2"

section galsum

theorem finsum_smul_eq_algebraMap_trace (K L : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G L] [IsGaloisGroup G K L] (y : L) :
    ∑ᶠ σ : G, σ • y = algebraMap K L (Algebra.trace K L y) := by
  classical
  haveI := Fintype.ofFinite G
  rw [finsum_eq_sum_of_fintype, trace_eq_sum_automorphisms,
    ← Fintype.sum_equiv (IsGaloisGroup.mulEquivAlgEquiv G K L).toEquiv (fun σ : G => σ • y) (fun τ : (L ≃ₐ[K] L) => τ y)]
  intro σ
  simp [IsGaloisGroup.mulEquivAlgEquiv]
end galsum
p2m_reactivate "P2MW.S_NumberField_PlaceDecomp_exists_finprod_smul_eq_of_valuation_sub_one_le_of_jump_lt_of_prime_card_decomp.Ws45 P2MW.S_NumberField_PlaceDecomp_exists_finprod_smul_eq_of_valuation_sub_one_le_of_jump_lt_of_prime_card_decomp.Ws45.CL2"

end IsDiscreteValuationRing.TraceOntoSol
p2m_reactivate "P2MW.S_NumberField_PlaceDecomp_exists_finprod_smul_eq_of_valuation_sub_one_le_of_jump_lt_of_prime_card_decomp.Ws45 P2MW.S_NumberField_PlaceDecomp_exists_finprod_smul_eq_of_valuation_sub_one_le_of_jump_lt_of_prime_card_decomp.Ws45.CL2"
p2m_reactivate "P2MW.S_NumberField_PlaceDecomp_exists_finprod_smul_eq_of_valuation_sub_one_le_of_jump_lt_of_prime_card_decomp.Ws45 P2MW.S_NumberField_PlaceDecomp_exists_finprod_smul_eq_of_valuation_sub_one_le_of_jump_lt_of_prime_card_decomp.Ws45.CL2"

p2m_open_scoped "IsDiscreteValuationRing" in
open IsDiscreteValuationRing.TraceOntoSol in

set_option maxHeartbeats 3200000 in
theorem IsDiscreteValuationRing.exists_finsum_smul_eq_of_mem_maximalIdeal_pow_of_lowerRamificationGroup_eq_top_of_eq_bot
    {B : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G B] [FaithfulSMul G B]
    [(IsLocalRing.maximalIdeal B).LiesOver (IsLocalRing.maximalIdeal (FixedPoints.subring B G))]
    [Algebra.IsSeparable
      (FixedPoints.subring B G ⧸ IsLocalRing.maximalIdeal (FixedPoints.subring B G))
      (B ⧸ IsLocalRing.maximalIdeal B)]
    (t : ℕ) (ht : IsLocalRing.lowerRamificationGroup B G t = ⊤)
    (ht' : IsLocalRing.lowerRamificationGroup B G (t + 1) = ⊥)
    (m : ℕ) (c : B) (hcG : ∀ σ : G, σ • c = c)
    (hc : c ∈ IsLocalRing.maximalIdeal B ^ (Nat.card G * ((m + (t + 1) * (Nat.card G - 1)) / Nat.card G))) :
    ∃ y : B, y ∈ IsLocalRing.maximalIdeal B ^ m ∧ ∑ᶠ σ : G, σ • y = c := by
  classical

  let A := FixedPoints.subring B G
  let K := FractionRing A
  let L := FractionRing B
  haveI : IsDiscreteValuationRing A := FixedPoints.isDiscreteValuationRing_subring
  haveI hGAB : IsGaloisGroup G A B := FixedPoints.isGaloisGroup_subring
  haveI : SMulCommClass G A B := hGAB.commutes
  haveI : Algebra.IsInvariant A B G := hGAB.isInvariant
  haveI : NoZeroSMulDivisors A B :=
    ⟨fun {a y} h => by
      rcases mul_eq_zero.mp (show (a : B) * y = 0 from h) with ha | hy
      · exact Or.inl (Subtype.ext ha)
      · exact Or.inr hy⟩
  letI := IsFractionRing.mulSemiringAction G B L
  haveI : SMulDistribClass G B L := IsFractionRing.smulDistribClass G B L
  haveI hGal : IsGaloisGroup G K L := IsGaloisGroup.toFractionRing G A B
  haveI := IsGaloisGroup.finiteDimensional G K L
  haveI := IsGaloisGroup.isGalois G K L
  haveI : Algebra.IsIntegral A B := Algebra.IsInvariant.isIntegral A B G
  haveI : Module.Finite A B := IsIntegralClosure.finite A K L B
  haveI : Fintype G := Fintype.ofFinite G

  have hG0 : IsLocalRing.lowerRamificationGroup B G 0 = ⊤ :=
    top_le_iff.mp (ht ▸ IsLocalRing.lowerRamificationGroup_antitone (Nat.zero_le t))
  have hcard0 : IsLocalRing.lowerRamificationCard B G 0 = Nat.card G := by
    rw [IsLocalRing.lowerRamificationCard, hG0, Subgroup.card_top]
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hval : IsDiscreteValuationRing.addVal B (ϖ : B) = (Nat.card G : ℕ∞) := by
    rw [IsDiscreteValuationRing.addVal_coe_eq_lowerRamificationCard_zero_mul_addVal_fixedPoints ϖ, hcard0,
      IsDiscreteValuationRing.addVal_uniformizer hϖ, mul_one]
  have hϖB : Ideal.span {algebraMap A B ϖ} = IsLocalRing.maximalIdeal B ^ Nat.card G :=
    span_singleton_eq_maximalIdeal_pow_of_addVal_eq hval
  have hϖ0 : algebraMap A B ϖ ≠ 0 := fun h0 =>
    hϖ.ne_zero (Subtype.coe_injective (h0.trans (ZeroMemClass.coe_zero _).symm))

  haveI hlocG : IsLocalHom (algebraMap A B) :=
    ⟨fun a h => (FixedPoints.isUnit_subring_iff a).mpr h⟩
  haveI : Algebra.IsSeparable (ResidueField A) (ResidueField B) :=
    (inferInstance : Algebra.IsSeparable
      (FixedPoints.subring B G ⧸ IsLocalRing.maximalIdeal (FixedPoints.subring B G))
      (B ⧸ IsLocalRing.maximalIdeal B))
  obtain ⟨θ, hθB⟩ := IsDiscreteValuationRing.exists_adjoin_singleton_eq_top_of_isSeparable_residueField
    (A := A) (B := B) Subtype.coe_injective
  have hθint : IsIntegral A θ := Algebra.IsIntegral.isIntegral θ

  have hsplit : (minpoly A θ).map (algebraMap A B) = ∏ σ : G, (X - C (σ • θ)) :=
    map_minpoly_eq_prod_X_sub_C_smul hθB hθint
  have hθL : Algebra.adjoin K {algebraMap B L θ} = ⊤ :=
    adjoin_algebraMap_eq_top hθB (hθint.algebraMap (B := L)).tower_top
  have hdiff : differentIdeal A B = ∏ σ ∈ Finset.univ.erase (1 : G), Ideal.span {σ • θ - θ} :=
    differentIdeal_eq_prod_span_smul_sub A K L B G θ hθL hθB hsplit
  have hdiff' : differentIdeal A B = IsLocalRing.maximalIdeal B ^ ((t + 1) * (Nat.card G - 1)) := by
    rw [hdiff, Finset.prod_congr rfl fun σ hσ =>
      span_smul_sub_eq_maximalIdeal_pow (A := A) hθB t ht ht' (Finset.ne_of_mem_erase hσ),
      Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ← pow_mul,
      Nat.card_eq_fintype_card]

  have hℓ0 : 0 < Nat.card G := Nat.card_pos
  have hc' : c ∈ Ideal.span {algebraMap A B ϖ ^ ((m + (t + 1) * (Nat.card G - 1)) / Nat.card G)} := by
    rw [← Ideal.span_singleton_pow, hϖB, ← pow_mul]
    exact hc
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp hc'
  have hbG : ∀ σ : G, σ • b = b := by
    intro σ
    have h1 := hcG σ
    rw [hb, smul_mul', ← map_pow, smul_algebraMap] at h1
    exact mul_left_cancel₀ (by rw [map_pow]; exact pow_ne_zero _ hϖ0) h1
  let bA : A := ⟨b, (FixedPoints.mem_subring_iff).mpr hbG⟩
  obtain ⟨y, hy, htr⟩ := exists_mem_pow_and_trace_eq (K := K) (L := L) hdiff' hϖ hϖB hℓ0 m bA
  refine ⟨y, hy, ?_⟩
  apply IsFractionRing.injective B L
  have hsum : algebraMap B L (∑ σ : G, σ • y) = algebraMap K L (Algebra.trace K L (algebraMap B L y)) := by
    rw [← finsum_smul_eq_algebraMap_trace K L G, finsum_eq_sum_of_fintype, map_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    exact algebraMap.smul' σ y L
  rw [finsum_eq_sum_of_fintype, hsum, htr, ← IsScalarTower.algebraMap_apply A K L, IsScalarTower.algebraMap_apply A B L,
    map_mul, map_pow, hb]
  rfl

end S1_inlined
p2m_reactivate "P2MW.S_NumberField_PlaceDecomp_exists_finprod_smul_eq_of_valuation_sub_one_le_of_jump_lt_of_prime_card_decomp.Ws45 P2MW.S_NumberField_PlaceDecomp_exists_finprod_smul_eq_of_valuation_sub_one_le_of_jump_lt_of_prime_card_decomp.Ws45.CL2"

section S2_inlined

namespace Ws45
namespace S2

open IsLocalRing
open scoped Pointwise

variable {B : Type*} [CommRing B] [IsLocalRing B] {G : Type*} [Group G] [MulSemiringAction G B]

theorem prod_mem_pow {ι : Type*} (I : Ideal B) (s : Finset ι) (f : ι → B) (hf : ∀ i ∈ s, f i ∈ I) :
    ∏ i ∈ s, f i ∈ I ^ s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, pow_succ']
    exact Ideal.mul_mem_mul (hf a (Finset.mem_insert_self a s)) (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem smul_mem_maximalIdeal_pow {k : ℕ} (σ : G) {x : B} (hx : x ∈ maximalIdeal B ^ k) : σ • x ∈ maximalIdeal B ^ k := by
  rw [← pointwise_smul_maximalIdeal_pow (R := B) σ k]
  exact Ideal.smul_mem_pointwise_smul σ x _ hx

end Ws45.S2
p2m_reactivate "P2MW.S_NumberField_PlaceDecomp_exists_finprod_smul_eq_of_valuation_sub_one_le_of_jump_lt_of_prime_card_decomp.Ws45 P2MW.S_NumberField_PlaceDecomp_exists_finprod_smul_eq_of_valuation_sub_one_le_of_jump_lt_of_prime_card_decomp.Ws45.CL2"
p2m_reactivate "P2MW.S_NumberField_PlaceDecomp_exists_finprod_smul_eq_of_valuation_sub_one_le_of_jump_lt_of_prime_card_decomp.Ws45 P2MW.S_NumberField_PlaceDecomp_exists_finprod_smul_eq_of_valuation_sub_one_le_of_jump_lt_of_prime_card_decomp.Ws45.CL2"

p2m_open_scoped "IsDiscreteValuationRing" in
theorem IsDiscreteValuationRing.exists_sub_one_mem_and_finprod_smul_sub_mem_of_jump_lt_of_prime_card
    {B : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G B] [FaithfulSMul G B]
    [(IsLocalRing.maximalIdeal B).LiesOver (IsLocalRing.maximalIdeal (FixedPoints.subring B G))]
    [Algebra.IsSeparable
      (FixedPoints.subring B G ⧸ IsLocalRing.maximalIdeal (FixedPoints.subring B G))
      (B ⧸ IsLocalRing.maximalIdeal B)]
    (hℓ : (Nat.card G).Prime)
    (t : ℕ) (ht : IsLocalRing.lowerRamificationGroup B G t = ⊤)
    (ht' : IsLocalRing.lowerRamificationGroup B G (t + 1) = ⊥)
    (n : ℕ) (hn : t < n) (a : FixedPoints.subring B G)
    (ha : (a : B) - 1 ∈ IsLocalRing.maximalIdeal B ^ (Nat.card G * n)) :
    ∃ b : B, b - 1 ∈ IsLocalRing.maximalIdeal B ^ (t + Nat.card G * (n - t)) ∧
      (∏ᶠ σ : G, σ • b) - a ∈ IsLocalRing.maximalIdeal B ^ (Nat.card G * (n + 1)) := by
  classical
  haveI := Fintype.ofFinite G
  set ℓ := Nat.card G with hℓdef
  have hℓ2 : 2 ≤ ℓ := hℓ.two_le
  have htn : t ≤ n := hn.le
  set ψ := t + ℓ * (n - t) with hψ

  have hmul : 2 * (n - t) ≤ ℓ * (n - t) := Nat.mul_le_mul_right _ hℓ2
  have hψn : n + 1 ≤ ψ := by omega
  have hr : (ψ + (t + 1) * (ℓ - 1)) / ℓ = n := by
    have : ψ + (t + 1) * (ℓ - 1) = ℓ * n + (ℓ - 1) := by
      rw [hψ]
      zify [htn, (by omega : 1 ≤ ℓ)]
      ring
    rw [this, Nat.add_comm, Nat.add_mul_div_left _ _ (by omega : 0 < ℓ), Nat.div_eq_of_lt (by omega : ℓ - 1 < ℓ), zero_add]
  have hr2 : n + 1 ≤ (2 * ψ + (t + 1) * (ℓ - 1)) / ℓ := by
    rw [Nat.le_div_iff_mul_le (by omega : 0 < ℓ)]
    have hnt : 1 ≤ ℓ * (n - t) + t := by nlinarith
    have : 2 * ψ + (t + 1) * (ℓ - 1) = ℓ * (n + 1) + (ℓ * (n - t) + t - 1) := by
      rw [hψ]
      zify [htn, (by omega : 1 ≤ ℓ), hnt]
      ring
    rw [this, mul_comm]
    exact Nat.le_add_right _ _

  have hcG : ∀ σ : G, σ • ((a : B) - 1) = (a : B) - 1 := fun σ => by
    rw [smul_sub, smul_one, a.2 σ]
  have hc : (a : B) - 1 ∈ IsLocalRing.maximalIdeal B ^ (ℓ * ((ψ + (t + 1) * (ℓ - 1)) / ℓ)) := by
    rw [hr]; exact ha
  obtain ⟨y, hy, hyTr⟩ :=
    IsDiscreteValuationRing.exists_finsum_smul_eq_of_mem_maximalIdeal_pow_of_lowerRamificationGroup_eq_top_of_eq_bot
      t ht ht' ψ ((a : B) - 1) hcG hc

  obtain ⟨δ, hδ, hexp⟩ := prod_one_add_smul_eq_one_add_finsum_add_finprod_add_finsum_smul_of_prime_card (B := B) (G := G) hℓ y
  refine ⟨1 + y, by rw [add_sub_cancel_left]; exact hy, ?_⟩

  have hb : ∏ᶠ σ : G, σ • (1 + y) = ∏ᶠ σ : G, (1 + σ • y) :=
    finprod_congr fun σ => by rw [smul_add, smul_one]
  have hkey : (∏ᶠ σ : G, σ • (1 + y)) - a = ∏ᶠ σ : G, σ • y + ∑ᶠ σ : G, σ • δ := by
    rw [hb, hexp, hyTr]; ring
  rw [hkey]
  refine Ideal.add_mem _ ?_ ?_
  ·
    rw [finprod_eq_prod_of_fintype]
    have h1 := Ws45.S2.prod_mem_pow (IsLocalRing.maximalIdeal B ^ ψ) (Finset.univ : Finset G) (fun σ => σ • y)
      fun σ _ => Ws45.S2.smul_mem_maximalIdeal_pow σ hy
    have hcardu : (Finset.univ : Finset G).card = ℓ := by rw [Finset.card_univ, hℓdef, Nat.card_eq_fintype_card]
    rw [← pow_mul, hcardu] at h1
    exact Ideal.pow_le_pow_right (by nlinarith) h1
  ·
    have hδ2 : δ ∈ IsLocalRing.maximalIdeal B ^ (2 * ψ) := by
      refine (Ideal.span_le.2 ?_) hδ
      rintro x ⟨σ₁, σ₂, -, rfl⟩
      rw [two_mul, pow_add]
      exact Ideal.mul_mem_mul (Ws45.S2.smul_mem_maximalIdeal_pow σ₁ hy) (Ws45.S2.smul_mem_maximalIdeal_pow σ₂ hy)
    have h2 := IsDiscreteValuationRing.finsum_smul_mem_maximalIdeal_pow_of_lowerRamificationGroup_eq_top_of_eq_bot
      t ht ht' (2 * ψ) δ hδ2
    exact Ideal.pow_le_pow_right (Nat.mul_le_mul_left _ hr2) h2

end S2_inlined
p2m_reactivate "P2MW.S_NumberField_PlaceDecomp_exists_finprod_smul_eq_of_valuation_sub_one_le_of_jump_lt_of_prime_card_decomp.Ws45 P2MW.S_NumberField_PlaceDecomp_exists_finprod_smul_eq_of_valuation_sub_one_le_of_jump_lt_of_prime_card_decomp.Ws45.CL2"

namespace Ws45
namespace XCL6

variable (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F]
  (w : IsDedekindDomain.HeightOneSpectrum (𝓞 F))

theorem isDiscreteValuationRing : IsDiscreteValuationRing ↥(w.valuation F).valuationSubring :=
  (w.valuation F).valuationSubring_isDiscreteValuationRing

theorem faithfulSMul_decomp_valuationSubring :
    FaithfulSMul ↥(NumberField.PlaceDecomp.decomp E F w) ↥(w.valuation F).valuationSubring := by
  refine ⟨fun {σ τ} h => Subtype.ext (AlgEquiv.ext fun m => ?_)⟩
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 F) m
  have hmem : ∀ r : 𝓞 F, (r : F) ∈ (w.valuation F).valuationSubring := fun r =>
    (Valuation.mem_valuationSubring_iff _ _).2 (w.valuation_le_one r)
  have h' : ∀ r : 𝓞 F, (σ : F ≃ₐ[E] F) (r : F) = (τ : F ≃ₐ[E] F) (r : F) := fun r =>
    congrArg (fun y : ↥(w.valuation F).valuationSubring => (y : F)) (h ⟨(r : F), hmem r⟩)
  rw [map_div₀, map_div₀]
  change (σ : F ≃ₐ[E] F) (a : F) / (σ : F ≃ₐ[E] F) (b : F) = (τ : F ≃ₐ[E] F) (a : F) / (τ : F ≃ₐ[E] F) (b : F)
  rw [h' a, h' b]

theorem liesOver_maximalIdeal_fixedPoints :
    (IsLocalRing.maximalIdeal ↥(w.valuation F).valuationSubring).LiesOver
      (IsLocalRing.maximalIdeal (FixedPoints.subring ↥(w.valuation F).valuationSubring
        ↥(NumberField.PlaceDecomp.decomp E F w))) :=
  ⟨FixedPoints.maximalIdeal_subring_eq_comap⟩

theorem exists_sub_algebraMap_lt_one (k : F) (hk : w.valuation F k ≤ 1) :
    ∃ r : 𝓞 F, w.valuation F (k - algebraMap (𝓞 F) F r) < 1 := by
  classical
  have hkmem : k ∈ IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime F w := by
    rw [IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]; exact hk
  obtain ⟨a, s, hs, hks⟩ : ∃ (a s : 𝓞 F) (_ : s ∈ w.asIdeal.primeCompl),
      k = algebraMap (𝓞 F) F a * (algebraMap (𝓞 F) F s)⁻¹ := hkmem
  have hs' : s ∉ w.asIdeal := hs
  haveI := w.isMaximal
  letI := Ideal.Quotient.field w.asIdeal
  obtain ⟨t, ht⟩ : ∃ t : 𝓞 F, s * t - 1 ∈ w.asIdeal := by
    have hs0 : (Ideal.Quotient.mk w.asIdeal s) ≠ 0 := by
      rwa [ne_eq, Ideal.Quotient.eq_zero_iff_mem]
    obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective ((Ideal.Quotient.mk w.asIdeal s)⁻¹)
    refine ⟨t, ?_⟩
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, map_mul, ht, mul_inv_cancel₀ hs0, sub_self]
  refine ⟨a * t, ?_⟩
  have hvs : w.valuation F (algebraMap (𝓞 F) F s) = 1 := by
    rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
    exact (IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff).2 hs'
  have hs0K : algebraMap (𝓞 F) F s ≠ 0 := by
    intro h; rw [h, map_zero] at hvs; exact zero_ne_one hvs
  have hrw : k - algebraMap (𝓞 F) F (a * t) =
      algebraMap (𝓞 F) F a * (algebraMap (𝓞 F) F s)⁻¹ * (1 - algebraMap (𝓞 F) F (s * t)) := by
    rw [hks, map_mul, map_mul]; field_simp
  rw [hrw, map_mul, map_mul, map_inv₀, hvs, inv_one, mul_one]
  calc w.valuation F (algebraMap (𝓞 F) F a) * w.valuation F (1 - algebraMap (𝓞 F) F (s * t))
      ≤ 1 * w.valuation F (1 - algebraMap (𝓞 F) F (s * t)) := by
        gcongr; exact w.valuation_le_one a
    _ < 1 := by
        have ht' : 1 - s * t ∈ w.asIdeal := by rw [← neg_sub]; exact w.asIdeal.neg_mem ht
        rw [one_mul, ← map_one (algebraMap (𝓞 F) F), ← map_sub,
          IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem]
        exact ht'

theorem finite_residueField : Finite (IsLocalRing.ResidueField ↥(w.valuation F).valuationSubring) := by
  classical
  haveI := w.isMaximal
  let ψ : 𝓞 F → IsLocalRing.ResidueField ↥(w.valuation F).valuationSubring := fun r =>
    IsLocalRing.residue _ ⟨algebraMap (𝓞 F) F r, (Valuation.mem_valuationSubring_iff _ _).2 (w.valuation_le_one r)⟩
  have hψ : Function.Surjective ψ := by
    intro xbar
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective xbar
    obtain ⟨r, hr⟩ := exists_sub_algebraMap_lt_one F w (x : F) ((Valuation.mem_valuationSubring_iff _ _).1 x.2)
    refine ⟨r, ?_⟩
    show IsLocalRing.residue _ _ = IsLocalRing.residue _ x
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, Valuation.mem_maximalIdeal_iff]
    show w.valuation F (algebraMap (𝓞 F) F r - (x : F)) < 1
    rw [Valuation.map_sub_swap]
    exact hr

  have hker : ∀ r₁ r₂ : 𝓞 F, r₁ - r₂ ∈ w.asIdeal → ψ r₁ = ψ r₂ := by
    intro r₁ r₂ h
    show IsLocalRing.residue _ _ = IsLocalRing.residue _ _
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, Valuation.mem_maximalIdeal_iff]
    show w.valuation F (algebraMap (𝓞 F) F r₁ - algebraMap (𝓞 F) F r₂) < 1
    rw [← map_sub, IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem]
    exact h
  haveI : Finite (𝓞 F ⧸ w.asIdeal) := inferInstance
  refine Finite.of_surjective (fun q : 𝓞 F ⧸ w.asIdeal => Quotient.liftOn' q ψ fun a b hab => hker a b ?_) ?_
  · rw [Submodule.quotientRel_def] at hab; exact hab
  · intro y
    obtain ⟨r, rfl⟩ := hψ y
    exact ⟨Ideal.Quotient.mk _ r, rfl⟩

theorem perfectField_residueField : PerfectField (IsLocalRing.ResidueField ↥(w.valuation F).valuationSubring) := by
  haveI := finite_residueField F w
  haveI := Fintype.ofFinite (IsLocalRing.ResidueField ↥(w.valuation F).valuationSubring)
  infer_instance

theorem isSeparable_residue_fixedPoints :
    letI := liesOver_maximalIdeal_fixedPoints E F w
    Algebra.IsSeparable
      (FixedPoints.subring ↥(w.valuation F).valuationSubring ↥(NumberField.PlaceDecomp.decomp E F w) ⧸
        IsLocalRing.maximalIdeal (FixedPoints.subring ↥(w.valuation F).valuationSubring
          ↥(NumberField.PlaceDecomp.decomp E F w)))
      (↥(w.valuation F).valuationSubring ⧸ IsLocalRing.maximalIdeal ↥(w.valuation F).valuationSubring) := by
  haveI := liesOver_maximalIdeal_fixedPoints E F w
  letI : Field (↥(w.valuation F).valuationSubring ⧸ IsLocalRing.maximalIdeal ↥(w.valuation F).valuationSubring) :=
    Ideal.Quotient.field _
  letI : Field (FixedPoints.subring ↥(w.valuation F).valuationSubring ↥(NumberField.PlaceDecomp.decomp E F w) ⧸
        IsLocalRing.maximalIdeal (FixedPoints.subring ↥(w.valuation F).valuationSubring
          ↥(NumberField.PlaceDecomp.decomp E F w))) := Ideal.Quotient.field _
  haveI : Finite (↥(w.valuation F).valuationSubring ⧸ IsLocalRing.maximalIdeal ↥(w.valuation F).valuationSubring) :=
    finite_residueField F w
  haveI : Finite (FixedPoints.subring ↥(w.valuation F).valuationSubring ↥(NumberField.PlaceDecomp.decomp E F w) ⧸
        IsLocalRing.maximalIdeal (FixedPoints.subring ↥(w.valuation F).valuationSubring
          ↥(NumberField.PlaceDecomp.decomp E F w))) :=
    Finite.of_injective _ (algebraMap _ (↥(w.valuation F).valuationSubring ⧸
      IsLocalRing.maximalIdeal ↥(w.valuation F).valuationSubring)).injective
  haveI := Fintype.ofFinite (FixedPoints.subring ↥(w.valuation F).valuationSubring ↥(NumberField.PlaceDecomp.decomp E F w) ⧸
        IsLocalRing.maximalIdeal (FixedPoints.subring ↥(w.valuation F).valuationSubring
          ↥(NumberField.PlaceDecomp.decomp E F w)))
  haveI : Module.Finite (FixedPoints.subring ↥(w.valuation F).valuationSubring ↥(NumberField.PlaceDecomp.decomp E F w) ⧸
        IsLocalRing.maximalIdeal (FixedPoints.subring ↥(w.valuation F).valuationSubring
          ↥(NumberField.PlaceDecomp.decomp E F w)))
      (↥(w.valuation F).valuationSubring ⧸ IsLocalRing.maximalIdeal ↥(w.valuation F).valuationSubring) :=
    Module.Finite.of_finite
  exact Algebra.IsAlgebraic.isSeparable_of_perfectField

section ram
variable [IsGalois E F] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 E)) (hw : w.under (𝓞 E) = v)

theorem inertiaSubgroup_eq_top (t : ℕ)
    (ht : ((w.valuation F).valuationSubring).lowerRamificationGroup E t = ⊤) :
    ((w.valuation F).valuationSubring).inertiaSubgroup E = ⊤ := by
  rw [← ValuationSubring.lowerRamificationGroup_zero]
  exact top_le_iff.1 (ht ▸ ValuationSubring.lowerRamificationGroup_antitone (Nat.zero_le t))

include hw in

theorem ramificationIdx_eq_natCard_decomp (t : ℕ)
    (ht : ((w.valuation F).valuationSubring).lowerRamificationGroup E t = ⊤) :
    v.asIdeal.ramificationIdx' w.asIdeal = Nat.card ↥(NumberField.PlaceDecomp.decomp E F w) := by
  haveI := w.isMaximal
  haveI := v.isMaximal
  haveI : w.asIdeal.LiesOver v.asIdeal := ⟨by rw [← hw]; rfl⟩

  have hI : w.asIdeal.inertia (F ≃ₐ[E] F) = NumberField.PlaceDecomp.decomp E F w := by
    rw [← IsDedekindDomain.HeightOneSpectrum.map_subtype_inertiaSubgroup_valuationSubring_eq_inertia E F w,
      inertiaSubgroup_eq_top E F w t ht, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

  letI := Ideal.Quotient.field v.asIdeal
  letI := Ideal.Quotient.field w.asIdeal
  haveI := Fintype.ofFinite (𝓞 E ⧸ v.asIdeal)
  haveI : PerfectField (𝓞 E ⧸ v.asIdeal) := inferInstance
  haveI : Algebra.IsSeparable (𝓞 E ⧸ v.asIdeal) (𝓞 F ⧸ w.asIdeal) := Algebra.IsAlgebraic.isSeparable_of_perfectField
  have e := Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal w.asIdeal v.ne_bot
  rw [e, ← Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal w.asIdeal (F ≃ₐ[E] F),
    ← Ideal.card_inertia_eq_ramificationIdxIn (G := F ≃ₐ[E] F) v.asIdeal w.asIdeal, hI]

include hw in

theorem valued_adicCompletionSemialgHom_eq_pow_natCard (t : ℕ)
    (ht : ((w.valuation F).valuationSubring).lowerRamificationGroup E t = ⊤) (a : v.adicCompletion E) :
    Valued.v (IsDedekindDomain.HeightOneSpectrum.Extension.adicCompletionSemialgHom E F (⟨w, hw⟩ : v.Extension (𝓞 F)) a) =
      Valued.v a ^ Nat.card ↥(NumberField.PlaceDecomp.decomp E F w) := by
  rw [IsDedekindDomain.HeightOneSpectrum.Extension.valued_adicCompletionSemialgHom]
  have h : ((⟨w, hw⟩ : v.Extension (𝓞 F)).1.under (𝓞 E)).asIdeal = v.asIdeal := by
    show (w.under (𝓞 E)).asIdeal = v.asIdeal; rw [hw]
  rw [h, ramificationIdx_eq_natCard_decomp E F w v hw t ht]

end ram
p2m_reactivate "P2MW.S_NumberField_PlaceDecomp_exists_finprod_smul_eq_of_valuation_sub_one_le_of_jump_lt_of_prime_card_decomp.Ws45 P2MW.S_NumberField_PlaceDecomp_exists_finprod_smul_eq_of_valuation_sub_one_le_of_jump_lt_of_prime_card_decomp.Ws45.CL2"

end Ws45.XCL6
p2m_reactivate "P2MW.S_NumberField_PlaceDecomp_exists_finprod_smul_eq_of_valuation_sub_one_le_of_jump_lt_of_prime_card_decomp.Ws45 P2MW.S_NumberField_PlaceDecomp_exists_finprod_smul_eq_of_valuation_sub_one_le_of_jump_lt_of_prime_card_decomp.Ws45.CL2"
p2m_reactivate "P2MW.S_NumberField_PlaceDecomp_exists_finprod_smul_eq_of_valuation_sub_one_le_of_jump_lt_of_prime_card_decomp.Ws45 P2MW.S_NumberField_PlaceDecomp_exists_finprod_smul_eq_of_valuation_sub_one_le_of_jump_lt_of_prime_card_decomp.Ws45.CL2"

namespace NumberField
p2m_export "NumberField" "mk PlaceDecomp.decomp PlaceDecomp.actRingEquiv PlaceDecomp.actRingEquiv_coe PlaceDecomp.continuous_actRingEquiv PlaceDecomp.smul_def PlaceDecomp.coe_smul_units PlaceDecomp.valued_smul PlaceDecomp.forall_smul_eq_iff_mem_range_adicCompletionSemialgHom"
namespace PlaceDecomp
p2m_export "NumberField.PlaceDecomp" "le_exp_neg_one_of_lt_one decomp actRingEquiv actRingEquiv_coe continuous_actRingEquiv smul_def coe_smul_units valued_smul forall_smul_eq_iff_mem_range_adicCompletionSemialgHom"
namespace XCNormL6
p2m_open "NumberField.PlaceDecomp NumberField"

theorem valued_prod_sub_prod_le {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    {ι : Type*} (s : Finset ι) (f g : ι → K) (ε : Γ₀)
    (hf : ∀ i ∈ s, Valued.v (f i) ≤ 1) (hg : ∀ i ∈ s, Valued.v (g i) ≤ 1)
    (hfg : ∀ i ∈ s, Valued.v (f i - g i) ≤ ε) :
    Valued.v (∏ i ∈ s, f i - ∏ i ∈ s, g i) ≤ ε ∨ s = ∅ := by
  classical
  induction s using Finset.induction_on with
  | empty => exact Or.inr rfl
  | insert a s ha ih =>
    left
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have hfa := hf a (Finset.mem_insert_self a s)
    have hga := hg a (Finset.mem_insert_self a s)
    have hpg : Valued.v (∏ i ∈ s, g i) ≤ 1 := by
      rw [map_prod]
      exact Finset.prod_le_one' fun i hi => hg i (Finset.mem_insert_of_mem hi)

    have hid : f a * ∏ i ∈ s, f i - g a * ∏ i ∈ s, g i =
        f a * (∏ i ∈ s, f i - ∏ i ∈ s, g i) + (f a - g a) * ∏ i ∈ s, g i := by ring
    rw [hid]
    refine le_trans (Valuation.map_add _ _ _) (max_le ?_ ?_)
    · rcases ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)) (fun i hi => hg i (Finset.mem_insert_of_mem hi))
          (fun i hi => hfg i (Finset.mem_insert_of_mem hi)) with h | h
      · rw [Valuation.map_mul]
        calc Valued.v (f a) * Valued.v (∏ i ∈ s, f i - ∏ i ∈ s, g i) ≤ 1 * ε := by gcongr
          _ = ε := one_mul ε
      · subst h
        simp only [Finset.prod_empty, sub_self, mul_zero, map_zero]
        exact zero_le'
    · rw [Valuation.map_mul]
      calc Valued.v (f a - g a) * Valued.v (∏ i ∈ s, g i) ≤ ε * 1 := by
            gcongr; exact hfg a (Finset.mem_insert_self a s)
        _ = ε := mul_one ε

end NumberField.PlaceDecomp.XCNormL6
p2m_reactivate "P2MW.S_NumberField_PlaceDecomp_exists_finprod_smul_eq_of_valuation_sub_one_le_of_jump_lt_of_prime_card_decomp.Ws45 P2MW.S_NumberField_PlaceDecomp_exists_finprod_smul_eq_of_valuation_sub_one_le_of_jump_lt_of_prime_card_decomp.Ws45.CL2"
p2m_reactivate "P2MW.S_NumberField_PlaceDecomp_exists_finprod_smul_eq_of_valuation_sub_one_le_of_jump_lt_of_prime_card_decomp.Ws45 P2MW.S_NumberField_PlaceDecomp_exists_finprod_smul_eq_of_valuation_sub_one_le_of_jump_lt_of_prime_card_decomp.Ws45.CL2"
p2m_reactivate "P2MW.S_NumberField_PlaceDecomp_exists_finprod_smul_eq_of_valuation_sub_one_le_of_jump_lt_of_prime_card_decomp.Ws45 P2MW.S_NumberField_PlaceDecomp_exists_finprod_smul_eq_of_valuation_sub_one_le_of_jump_lt_of_prime_card_decomp.Ws45.CL2"

namespace NumberField
p2m_export "NumberField" "mk PlaceDecomp.decomp PlaceDecomp.actRingEquiv PlaceDecomp.actRingEquiv_coe PlaceDecomp.continuous_actRingEquiv PlaceDecomp.smul_def PlaceDecomp.coe_smul_units PlaceDecomp.valued_smul PlaceDecomp.forall_smul_eq_iff_mem_range_adicCompletionSemialgHom"
namespace PlaceDecomp
p2m_export "NumberField.PlaceDecomp" "le_exp_neg_one_of_lt_one decomp actRingEquiv actRingEquiv_coe continuous_actRingEquiv smul_def coe_smul_units valued_smul forall_smul_eq_iff_mem_range_adicCompletionSemialgHom"
namespace XCNormL6
p2m_open "NumberField.PlaceDecomp NumberField"

open IsDedekindDomain.HeightOneSpectrum

section local_frame
variable (E F : Type) [Field E] [Field F] [NumberField F] [Algebra E F] (w : HeightOneSpectrum (𝓞 F))

theorem smul_coe (σ : ↥(NumberField.PlaceDecomp.decomp E F w)) (k : F) :
    σ • ((k : w.adicCompletion F)) = (((σ : F ≃ₐ[E] F) k : F) : w.adicCompletion F) := by
  rw [NumberField.PlaceDecomp.smul_def]
  show NumberField.PlaceDecomp.actRingEquiv σ
      ((WithVal.toVal (w.valuation F) k : WithVal (w.valuation F)) : w.adicCompletion F)
    = ((WithVal.toVal (w.valuation F) ((σ : F ≃ₐ[E] F) k) : WithVal (w.valuation F)) : w.adicCompletion F)
  rw [NumberField.PlaceDecomp.actRingEquiv_coe, WithVal.congr_apply]
  rfl

theorem le_exp_neg_one_of_lt_one {t : WithZero (Multiplicative ℤ)} (ht : t < 1) : t ≤ WithZero.exp (-1 : ℤ) := by
  rcases eq_or_ne t 0 with rfl | h0
  · exact zero_le'
  · obtain ⟨z, rfl⟩ : ∃ z : ℤ, t = WithZero.exp z := ⟨WithZero.log t, (WithZero.exp_log h0).symm⟩
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at ht
    rw [WithZero.exp_le_exp]
    omega

theorem valued_coe (k : F) : Valued.v (k : w.adicCompletion F) = w.valuation F k :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w k

theorem coe_sub (a b : F) : ((a - b : F) : w.adicCompletion F) = (a : w.adicCompletion F) - (b : w.adicCompletion F) :=
  map_sub (algebraMap F (w.adicCompletion F)) _ _

theorem coe_one' : ((1 : F) : w.adicCompletion F) = 1 := map_one (algebraMap F (w.adicCompletion F))

private theorem _root_.NumberField.PlaceDecomp.XCNormL6.coe_prod {ι : Type*} (s : Finset ι) (f : ι → F) :
    ((∏ i ∈ s, f i : F) : w.adicCompletion F) = ∏ i ∈ s, ((f i : F) : w.adicCompletion F) :=
  map_prod (algebraMap F (w.adicCompletion F)) _ _

p2m_export "NumberField.PlaceDecomp.XCNormL6" "coe_prod"

theorem exists_valued_sub_coe_lt_one (x : w.adicCompletion F) :
    ∃ k : F, Valued.v (x - (k : w.adicCompletion F)) < 1 := by
  have hopen : IsOpen {y : w.adicCompletion F | Valued.v (y - x) < 1} := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    rw [Valued.mem_nhds]
    refine ⟨1, fun z hz => ?_⟩
    have hz' : Valued.v (z - y) < 1 := by
      have h := hz
      simp only [Set.mem_setOf_eq, Units.val_one] at h
      exact (Valuation.restrict_lt_one_iff Valued.v).1 h
    show Valued.v (z - x) < 1
    calc Valued.v (z - x) = Valued.v (z - y + (y - x)) := by rw [sub_add_sub_cancel]
      _ ≤ max (Valued.v (z - y)) (Valued.v (y - x)) := Valuation.map_add _ _ _
      _ < 1 := max_lt hz' hy
  obtain ⟨k, hk⟩ := (HeightOneSpectrum.denseRange_algebraMap F w).exists_mem_open hopen ⟨x, by simp⟩
  refine ⟨k, ?_⟩
  rw [Valuation.map_sub_swap]
  exact hk

theorem exists_valued_sub_coe_le (x : w.adicCompletion F) (M : ℕ) :
    ∃ k : F, Valued.v (x - (k : w.adicCompletion F)) ≤ WithZero.exp (-(M : ℤ)) := by
  obtain ⟨π, hπ⟩ := w.valuation_exists_uniformizer F
  have hπv : Valued.v ((π : F) : w.adicCompletion F) = WithZero.exp (-1 : ℤ) := by rw [valued_coe]; exact hπ
  have hπ0 : ((π : F) : w.adicCompletion F) ≠ 0 := by
    intro h; rw [h, map_zero] at hπv; exact WithZero.coe_ne_zero hπv.symm
  obtain ⟨k, hk⟩ := exists_valued_sub_coe_lt_one F w (x * (((π : F) : w.adicCompletion F) ^ M)⁻¹)
  refine ⟨k * (π : F) ^ M, ?_⟩
  have hrw : x - ((k * (π : F) ^ M : F) : w.adicCompletion F) =
      (x * (((π : F) : w.adicCompletion F) ^ M)⁻¹ - (k : w.adicCompletion F)) * ((π : F) : w.adicCompletion F) ^ M := by
    have h1 : ((k * (π : F) ^ M : F) : w.adicCompletion F) = (k : w.adicCompletion F) * ((π : F) : w.adicCompletion F) ^ M :=
      (map_mul (algebraMap F (w.adicCompletion F)) k ((π : F) ^ M)).trans
        (congrArg (fun z => (k : w.adicCompletion F) * z) (map_pow (algebraMap F (w.adicCompletion F)) (π : F) M))
    rw [h1, sub_mul, mul_assoc, inv_mul_cancel₀ (pow_ne_zero M hπ0), mul_one]
  rw [hrw, map_mul, map_pow, hπv, ← WithZero.exp_nsmul, show M • (-1 : ℤ) = -(M : ℤ) by simp]
  calc Valued.v (x * (((π : F) : w.adicCompletion F) ^ M)⁻¹ - (k : w.adicCompletion F)) * WithZero.exp (-(M : ℤ))
      ≤ 1 * WithZero.exp (-(M : ℤ)) := by gcongr
    _ = WithZero.exp (-(M : ℤ)) := one_mul _

theorem mem_maximalIdeal_pow_iff (m : ℕ) (x : ↥((w.valuation F).valuationSubring)) :
    x ∈ IsLocalRing.maximalIdeal ↥((w.valuation F).valuationSubring) ^ m ↔
      w.valuation F (x : F) ≤ WithZero.exp (-(m : ℤ)) := by

  obtain ⟨π, hπ⟩ := w.valuation_exists_uniformizer F
  have hπv : w.valuation F (π : F) = WithZero.exp (-1 : ℤ) := hπ
  have hπmem : (π : F) ∈ (w.valuation F).valuationSubring := by
    rw [Valuation.mem_valuationSubring_iff, hπv, ← WithZero.exp_zero, WithZero.exp_le_exp]; norm_num
  set ϖ : ↥((w.valuation F).valuationSubring) := ⟨(π : F), hπmem⟩ with hϖ
  have hint : (w.valuation F).Integers ↥((w.valuation F).valuationSubring) := Valuation.integer.integers _

  have hmax : IsLocalRing.maximalIdeal ↥((w.valuation F).valuationSubring) = Ideal.span {ϖ} := by
    apply le_antisymm
    · intro y hy
      rw [Valuation.mem_maximalIdeal_iff] at hy
      have hle : w.valuation F (y : F) ≤ w.valuation F (ϖ : F) := by
        rw [hϖ]; show w.valuation F (y : F) ≤ w.valuation F (π : F); rw [hπv]
        exact le_exp_neg_one_of_lt_one hy
      exact Ideal.mem_span_singleton.mpr (hint.dvd_of_le hle)
    · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Valuation.mem_maximalIdeal_iff]
      show w.valuation F (π : F) < 1
      rw [hπv, ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  rw [hmax, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  have hvϖm : w.valuation F ((ϖ ^ m : ↥((w.valuation F).valuationSubring)) : F) = WithZero.exp (-(m : ℤ)) := by
    push_cast
    rw [map_pow]; show w.valuation F (π : F) ^ m = _
    rw [hπv, ← WithZero.exp_nsmul]; simp
  constructor
  · intro h
    rw [← hvϖm]
    exact hint.le_of_dvd h
  · intro h
    apply hint.dvd_of_le
    show w.valuation F (x : F) ≤ w.valuation F ((ϖ ^ m : ↥((w.valuation F).valuationSubring)) : F)
    rw [hvϖm]
    exact h

end local_frame
p2m_reactivate "P2MW.S_NumberField_PlaceDecomp_exists_finprod_smul_eq_of_valuation_sub_one_le_of_jump_lt_of_prime_card_decomp.Ws45 P2MW.S_NumberField_PlaceDecomp_exists_finprod_smul_eq_of_valuation_sub_one_le_of_jump_lt_of_prime_card_decomp.Ws45.CL2"

end NumberField.PlaceDecomp.XCNormL6
p2m_reactivate "P2MW.S_NumberField_PlaceDecomp_exists_finprod_smul_eq_of_valuation_sub_one_le_of_jump_lt_of_prime_card_decomp.Ws45 P2MW.S_NumberField_PlaceDecomp_exists_finprod_smul_eq_of_valuation_sub_one_le_of_jump_lt_of_prime_card_decomp.Ws45.CL2"
p2m_reactivate "P2MW.S_NumberField_PlaceDecomp_exists_finprod_smul_eq_of_valuation_sub_one_le_of_jump_lt_of_prime_card_decomp.Ws45 P2MW.S_NumberField_PlaceDecomp_exists_finprod_smul_eq_of_valuation_sub_one_le_of_jump_lt_of_prime_card_decomp.Ws45.CL2"
p2m_reactivate "P2MW.S_NumberField_PlaceDecomp_exists_finprod_smul_eq_of_valuation_sub_one_le_of_jump_lt_of_prime_card_decomp.Ws45 P2MW.S_NumberField_PlaceDecomp_exists_finprod_smul_eq_of_valuation_sub_one_le_of_jump_lt_of_prime_card_decomp.Ws45.CL2"

namespace NumberField
p2m_export "NumberField" "mk PlaceDecomp.decomp PlaceDecomp.actRingEquiv PlaceDecomp.actRingEquiv_coe PlaceDecomp.continuous_actRingEquiv PlaceDecomp.smul_def PlaceDecomp.coe_smul_units PlaceDecomp.valued_smul PlaceDecomp.forall_smul_eq_iff_mem_range_adicCompletionSemialgHom"
namespace PlaceDecomp
p2m_export "NumberField.PlaceDecomp" "le_exp_neg_one_of_lt_one decomp actRingEquiv actRingEquiv_coe continuous_actRingEquiv smul_def coe_smul_units valued_smul forall_smul_eq_iff_mem_range_adicCompletionSemialgHom"
namespace XCSurjLim
p2m_open "NumberField.PlaceDecomp NumberField"

open Filter Topology IsDedekindDomain.HeightOneSpectrum

section lim
variable (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F]
  (w : HeightOneSpectrum (𝓞 F))

noncomputable def cnorm (u : (w.adicCompletion F)) : (w.adicCompletion F) :=
  haveI : Fintype ↥(NumberField.PlaceDecomp.decomp E F w) := Fintype.ofFinite _
  ∏ σ : ↥(NumberField.PlaceDecomp.decomp E F w), σ • u

theorem cnorm_def [Fintype ↥(NumberField.PlaceDecomp.decomp E F w)] (u : (w.adicCompletion F)) : cnorm E F w u = ∏ σ : ↥(NumberField.PlaceDecomp.decomp E F w), σ • u := by
  unfold cnorm; congr; exact Subsingleton.elim _ _

theorem cnorm_mul (u u' : (w.adicCompletion F)) : cnorm E F w (u * u') = cnorm E F w u * cnorm E F w u' := by
  haveI : Fintype ↥(NumberField.PlaceDecomp.decomp E F w) := Fintype.ofFinite _
  simp only [cnorm_def, smul_mul', Finset.prod_mul_distrib]

theorem cnorm_one : cnorm E F w 1 = 1 := by
  haveI : Fintype ↥(NumberField.PlaceDecomp.decomp E F w) := Fintype.ofFinite _
  simp [cnorm_def]

theorem valued_cnorm {u : (w.adicCompletion F)} (hu : Valued.v u = 1) : Valued.v (cnorm E F w u) = 1 := by
  haveI : Fintype ↥(NumberField.PlaceDecomp.decomp E F w) := Fintype.ofFinite _
  rw [cnorm_def, map_prod]
  exact Finset.prod_eq_one fun σ _ => by rw [NumberField.PlaceDecomp.valued_smul, hu]

theorem smul_cnorm (τ : ↥(NumberField.PlaceDecomp.decomp E F w)) (u : (w.adicCompletion F)) : τ • cnorm E F w u = cnorm E F w u := by
  haveI : Fintype ↥(NumberField.PlaceDecomp.decomp E F w) := Fintype.ofFinite _
  rw [cnorm_def]; exact Finset.smul_prod_perm u τ

theorem continuous_cnorm : Continuous (cnorm E F w) := by
  haveI : Fintype ↥(NumberField.PlaceDecomp.decomp E F w) := Fintype.ofFinite _
  have h : cnorm E F w = fun u => ∏ σ : ↥(NumberField.PlaceDecomp.decomp E F w), σ • u := funext fun u => cnorm_def E F w u
  rw [h]
  exact continuous_finsetProd _ fun σ _ =>
    (NumberField.PlaceDecomp.continuous_actRingEquiv σ).congr fun u => (NumberField.PlaceDecomp.smul_def σ u).symm

theorem tendsto_of_valued_sub_le (x : ℕ → (w.adicCompletion F)) (a : (w.adicCompletion F)) (c : ℕ)
    (h : ∀ k, c ≤ k → Valued.v (x k - a) ≤ WithZero.exp (-(k : ℤ))) : Tendsto x atTop (𝓝 a) := by
  obtain ⟨π, hπ⟩ := w.valuation_exists_uniformizer F
  have hπv : Valued.v (π : (w.adicCompletion F)) = WithZero.exp (-1 : ℤ) := by
    rw [valuedAdicCompletion_eq_valuation', hπ]
  have hπn : ‖(π : (w.adicCompletion F))‖ < 1 := by
    rw [← norm_one (α := (w.adicCompletion F)), Valued.toNormedField.norm_lt_iff, hπv, map_one, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero_norm' (Filter.eventually_atTop.2 ⟨c, fun k hk => ?_⟩)
    (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hπn)
  rw [norm_norm, ← norm_pow, Valued.toNormedField.norm_le_iff, map_pow, hπv, ← WithZero.exp_nsmul]
  simpa using h k hk

variable (lev : ℕ → ℕ) (hlev : ∀ k, k ≤ lev k) (hmono : Monotone lev) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (m : ℕ)
  (hstep : ∀ k, m ≤ k → ∀ y : (w.adicCompletion F), Valued.v y = 1 → Valued.v (y - 1) ≤ WithZero.exp (-((ℓ * k : ℕ) : ℤ)) →
    (∀ τ : ↥(NumberField.PlaceDecomp.decomp E F w), τ • y = y) →
    ∃ u : (w.adicCompletion F), Valued.v u = 1 ∧ Valued.v (u - 1) ≤ WithZero.exp (-(lev k : ℤ)) ∧
      Valued.v (cnorm E F w u - y) ≤ WithZero.exp (-((ℓ * (k + 1) : ℕ) : ℤ)))
  (y₀ : (w.adicCompletion F)) (hy₀ : Valued.v y₀ = 1) (hy₀1 : Valued.v (y₀ - 1) ≤ WithZero.exp (-((ℓ * m : ℕ) : ℤ)))
  (hy₀fix : ∀ τ : ↥(NumberField.PlaceDecomp.decomp E F w), τ • y₀ = y₀)

def Inv (k : ℕ) (y : (w.adicCompletion F)) : Prop :=
  Valued.v y = 1 ∧ Valued.v (y - 1) ≤ WithZero.exp (-((ℓ * (m + k) : ℕ) : ℤ)) ∧ ∀ τ : ↥(NumberField.PlaceDecomp.decomp E F w), τ • y = y

include hstep in
theorem inv_succ (k : ℕ) (y : (w.adicCompletion F)) (hy : Inv E F w ℓ m k y) :
    Inv E F w ℓ m (k + 1) (y * (cnorm E F w (hstep (m + k) (Nat.le_add_right m k) y hy.1 hy.2.1 hy.2.2).choose)⁻¹) := by
  set u := (hstep (m + k) (Nat.le_add_right m k) y hy.1 hy.2.1 hy.2.2).choose with hu
  obtain ⟨hu1, -, huN⟩ := (hstep (m + k) (Nat.le_add_right m k) y hy.1 hy.2.1 hy.2.2).choose_spec
  have hN1 : Valued.v (cnorm E F w u) = 1 := valued_cnorm E F w hu1
  have hN0 : cnorm E F w u ≠ 0 := fun h => by rw [h, map_zero] at hN1; exact zero_ne_one hN1
  refine ⟨by rw [map_mul, map_inv₀, hy.1, hN1, inv_one, mul_one], ?_, fun τ => by rw [smul_mul', smul_inv'', smul_cnorm, hy.2.2 τ]⟩
  have hrw : y * (cnorm E F w u)⁻¹ - 1 = -((cnorm E F w u - y) * (cnorm E F w u)⁻¹) := by
    field_simp
    ring
  rw [hrw, Valuation.map_neg, map_mul, map_inv₀, hN1, inv_one, mul_one, show m + (k + 1) = m + k + 1 by ring]
  exact huN

noncomputable def Y : (k : ℕ) → {y : (w.adicCompletion F) // Inv E F w ℓ m k y}
  | 0 => ⟨y₀, hy₀, by simpa using hy₀1, hy₀fix⟩
  | k + 1 =>
    let ih := Y k
    ⟨_, inv_succ E F w lev ℓ m hstep k ih.1 ih.2⟩

noncomputable def U (k : ℕ) : (w.adicCompletion F) :=
  (hstep (m + k) (Nat.le_add_right m k) (Y E F w lev ℓ m hstep y₀ hy₀ hy₀1 hy₀fix k).1
    (Y E F w lev ℓ m hstep y₀ hy₀ hy₀1 hy₀fix k).2.1 (Y E F w lev ℓ m hstep y₀ hy₀ hy₀1 hy₀fix k).2.2.1
    (Y E F w lev ℓ m hstep y₀ hy₀ hy₀1 hy₀fix k).2.2.2).choose

theorem U_spec (k : ℕ) : Valued.v (U E F w lev ℓ m hstep y₀ hy₀ hy₀1 hy₀fix k) = 1 ∧
    Valued.v (U E F w lev ℓ m hstep y₀ hy₀ hy₀1 hy₀fix k - 1) ≤ WithZero.exp (-(lev (m + k) : ℤ)) ∧
    Valued.v (cnorm E F w (U E F w lev ℓ m hstep y₀ hy₀ hy₀1 hy₀fix k) - (Y E F w lev ℓ m hstep y₀ hy₀ hy₀1 hy₀fix k).1) ≤
      WithZero.exp (-((ℓ * (m + k + 1) : ℕ) : ℤ)) :=
  (hstep (m + k) (Nat.le_add_right m k) (Y E F w lev ℓ m hstep y₀ hy₀ hy₀1 hy₀fix k).1
    (Y E F w lev ℓ m hstep y₀ hy₀ hy₀1 hy₀fix k).2.1 (Y E F w lev ℓ m hstep y₀ hy₀ hy₀1 hy₀fix k).2.2.1
    (Y E F w lev ℓ m hstep y₀ hy₀ hy₀1 hy₀fix k).2.2.2).choose_spec

theorem Y_succ (k : ℕ) : (Y E F w lev ℓ m hstep y₀ hy₀ hy₀1 hy₀fix (k + 1)).1 =
    (Y E F w lev ℓ m hstep y₀ hy₀ hy₀1 hy₀fix k).1 * (cnorm E F w (U E F w lev ℓ m hstep y₀ hy₀ hy₀1 hy₀fix k))⁻¹ := rfl

theorem Y_zero : (Y E F w lev ℓ m hstep y₀ hy₀ hy₀1 hy₀fix 0).1 = y₀ := rfl

noncomputable def P (k : ℕ) : (w.adicCompletion F) := ∏ j ∈ Finset.range k, U E F w lev ℓ m hstep y₀ hy₀ hy₀1 hy₀fix j

theorem y₀_eq (k : ℕ) : y₀ = cnorm E F w (P E F w lev ℓ m hstep y₀ hy₀ hy₀1 hy₀fix k) *
    (Y E F w lev ℓ m hstep y₀ hy₀ hy₀1 hy₀fix k).1 := by
  induction k with
  | zero => rw [P, Finset.range_zero, Finset.prod_empty, cnorm_one, one_mul]; rfl
  | succ k ih =>
    rw [P, Finset.prod_range_succ, cnorm_mul, Y_succ, ← P]
    have hN1 : Valued.v (cnorm E F w (U E F w lev ℓ m hstep y₀ hy₀ hy₀1 hy₀fix k)) = 1 :=
      valued_cnorm E F w (U_spec E F w lev ℓ m hstep y₀ hy₀ hy₀1 hy₀fix k).1
    have hN0 : cnorm E F w (U E F w lev ℓ m hstep y₀ hy₀ hy₀1 hy₀fix k) ≠ 0 := fun h => by
      rw [h, map_zero] at hN1; exact zero_ne_one hN1
    have h : ∀ (a b c : (w.adicCompletion F)), b ≠ 0 → a * b * (c * b⁻¹) = a * c := by
      intro a b c hb; field_simp
    rw [h _ _ _ hN0]; exact ih

end lim
p2m_reactivate "P2MW.S_NumberField_PlaceDecomp_exists_finprod_smul_eq_of_valuation_sub_one_le_of_jump_lt_of_prime_card_decomp.Ws45 P2MW.S_NumberField_PlaceDecomp_exists_finprod_smul_eq_of_valuation_sub_one_le_of_jump_lt_of_prime_card_decomp.Ws45.CL2"

end NumberField.PlaceDecomp.XCSurjLim
p2m_reactivate "P2MW.S_NumberField_PlaceDecomp_exists_finprod_smul_eq_of_valuation_sub_one_le_of_jump_lt_of_prime_card_decomp.Ws45 P2MW.S_NumberField_PlaceDecomp_exists_finprod_smul_eq_of_valuation_sub_one_le_of_jump_lt_of_prime_card_decomp.Ws45.CL2"
p2m_reactivate "P2MW.S_NumberField_PlaceDecomp_exists_finprod_smul_eq_of_valuation_sub_one_le_of_jump_lt_of_prime_card_decomp.Ws45 P2MW.S_NumberField_PlaceDecomp_exists_finprod_smul_eq_of_valuation_sub_one_le_of_jump_lt_of_prime_card_decomp.Ws45.CL2"
p2m_reactivate "P2MW.S_NumberField_PlaceDecomp_exists_finprod_smul_eq_of_valuation_sub_one_le_of_jump_lt_of_prime_card_decomp.Ws45 P2MW.S_NumberField_PlaceDecomp_exists_finprod_smul_eq_of_valuation_sub_one_le_of_jump_lt_of_prime_card_decomp.Ws45.CL2"

namespace NumberField
p2m_export "NumberField" "mk PlaceDecomp.decomp PlaceDecomp.actRingEquiv PlaceDecomp.actRingEquiv_coe PlaceDecomp.continuous_actRingEquiv PlaceDecomp.smul_def PlaceDecomp.coe_smul_units PlaceDecomp.valued_smul PlaceDecomp.forall_smul_eq_iff_mem_range_adicCompletionSemialgHom"
namespace PlaceDecomp
p2m_export "NumberField.PlaceDecomp" "le_exp_neg_one_of_lt_one decomp actRingEquiv actRingEquiv_coe continuous_actRingEquiv smul_def coe_smul_units valued_smul forall_smul_eq_iff_mem_range_adicCompletionSemialgHom"
namespace XCSurjLim
p2m_open "NumberField.PlaceDecomp NumberField"

open Filter Topology IsDedekindDomain.HeightOneSpectrum

section lim2
variable (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F]
  (w : HeightOneSpectrum (𝓞 F))
  (lev : ℕ → ℕ) (ℓ : ℕ) (m : ℕ)
  (hstep : ∀ k, m ≤ k → ∀ y : (w.adicCompletion F), Valued.v y = 1 → Valued.v (y - 1) ≤ WithZero.exp (-((ℓ * k : ℕ) : ℤ)) →
    (∀ τ : ↥(NumberField.PlaceDecomp.decomp E F w), τ • y = y) →
    ∃ u : (w.adicCompletion F), Valued.v u = 1 ∧ Valued.v (u - 1) ≤ WithZero.exp (-(lev k : ℤ)) ∧
      Valued.v (cnorm E F w u - y) ≤ WithZero.exp (-((ℓ * (k + 1) : ℕ) : ℤ)))
  (y₀ : (w.adicCompletion F)) (hy₀ : Valued.v y₀ = 1) (hy₀1 : Valued.v (y₀ - 1) ≤ WithZero.exp (-((ℓ * m : ℕ) : ℤ)))
  (hy₀fix : ∀ τ : ↥(NumberField.PlaceDecomp.decomp E F w), τ • y₀ = y₀)

theorem valued_P (k : ℕ) : Valued.v (P E F w lev ℓ m hstep y₀ hy₀ hy₀1 hy₀fix k) = 1 := by
  rw [P, map_prod]
  exact Finset.prod_eq_one fun j _ => (U_spec E F w lev ℓ m hstep y₀ hy₀ hy₀1 hy₀fix j).1

theorem valued_P_sub_one (hmono : Monotone lev) (k : ℕ) :
    Valued.v (P E F w lev ℓ m hstep y₀ hy₀ hy₀1 hy₀fix k - 1) ≤ WithZero.exp (-(lev m : ℤ)) := by
  induction k with
  | zero => rw [P, Finset.range_zero, Finset.prod_empty, sub_self, map_zero]; exact zero_le'
  | succ k ih =>
    have hexp : P E F w lev ℓ m hstep y₀ hy₀ hy₀1 hy₀fix (k + 1) - 1 = P E F w lev ℓ m hstep y₀ hy₀ hy₀1 hy₀fix k * (U E F w lev ℓ m hstep y₀ hy₀ hy₀1 hy₀fix k - 1) + (P E F w lev ℓ m hstep y₀ hy₀ hy₀1 hy₀fix k - 1) := by
      rw [P, Finset.prod_range_succ, ← P]; ring
    rw [hexp]
    refine le_trans (Valuation.map_add _ _ _) (max_le ?_ ih)
    rw [map_mul, valued_P, one_mul]
    exact (U_spec E F w lev ℓ m hstep y₀ hy₀ hy₀1 hy₀fix k).2.1.trans (WithZero.exp_le_exp.mpr (neg_le_neg (by exact_mod_cast hmono (Nat.le_add_right m k))))

theorem tendsto_P (hlev : ∀ k, k ≤ lev k) :
    ∃ L : (w.adicCompletion F), Tendsto (fun k => P E F w lev ℓ m hstep y₀ hy₀ hy₀1 hy₀fix k) atTop (𝓝 L) := by
  refine cauchySeq_tendsto_of_complete (NonarchimedeanAddGroup.cauchySeq_of_tendsto_sub_nhds_zero ?_)
  refine tendsto_of_valued_sub_le F w _ 0 0 fun k _ => ?_
  rw [sub_zero]
  have hexp : P E F w lev ℓ m hstep y₀ hy₀ hy₀1 hy₀fix (k + 1) - P E F w lev ℓ m hstep y₀ hy₀ hy₀1 hy₀fix k = P E F w lev ℓ m hstep y₀ hy₀ hy₀1 hy₀fix k * (U E F w lev ℓ m hstep y₀ hy₀ hy₀1 hy₀fix k - 1) := by
    rw [P, Finset.prod_range_succ, ← P]; ring
  rw [hexp, map_mul, valued_P, one_mul]
  exact (U_spec E F w lev ℓ m hstep y₀ hy₀ hy₀1 hy₀fix k).2.1.trans (WithZero.exp_le_exp.mpr (neg_le_neg (by exact_mod_cast (hlev (m + k)).trans' (Nat.le_add_left k m))))

include hy₀ hy₀1 hy₀fix hstep in

theorem exists_cnorm_eq (hlev : ∀ k, k ≤ lev k) (hmono : Monotone lev) (hℓ : 1 ≤ ℓ) :
    ∃ b : (w.adicCompletion F), Valued.v b = 1 ∧ Valued.v (b - 1) ≤ WithZero.exp (-(lev m : ℤ)) ∧ cnorm E F w b = y₀ := by
  obtain ⟨L, hL⟩ := tendsto_P E F w lev ℓ m hstep y₀ hy₀ hy₀1 hy₀fix hlev

  have hL1 : Valued.v L = 1 := by
    have hclosed : IsClosed {x : (w.adicCompletion F) | Valued.v x = 1} := by
      have := Valued.isClosed_sphere (w.adicCompletion F) (Valued.v.restrict (1 : (w.adicCompletion F)))
      convert this using 2 with x
      simp
    exact hclosed.mem_of_tendsto hL (Filter.Eventually.of_forall fun k => valued_P E F w lev ℓ m hstep y₀ hy₀ hy₀1 hy₀fix k)
  have hLm : Valued.v (L - 1) ≤ WithZero.exp (-(lev m : ℤ)) := by
    obtain ⟨π, hπ⟩ := w.valuation_exists_uniformizer F
    have hπv : Valued.v ((π ^ lev m : F) : (w.adicCompletion F)) = WithZero.exp (-(lev m : ℤ)) := by
      rw [valuedAdicCompletion_eq_valuation', map_pow, hπ, ← WithZero.exp_nsmul]
      simp
    have hclosed : IsClosed {x : (w.adicCompletion F) | Valued.v (x - 1) ≤ WithZero.exp (-(lev m : ℤ))} := by
      have hc := Valued.isClosed_closedBall (w.adicCompletion F) (Valued.v.restrict (((π ^ lev m : F)) : (w.adicCompletion F)))
      have hc' : IsClosed ((fun x : (w.adicCompletion F) => x - 1) ⁻¹'
          {x | Valued.v.restrict x ≤ Valued.v.restrict (((π ^ lev m : F)) : (w.adicCompletion F))}) :=
        hc.preimage (continuous_sub_right 1)
      have hset : {x : (w.adicCompletion F) | Valued.v (x - 1) ≤ WithZero.exp (-(lev m : ℤ))} =
          ((fun x : (w.adicCompletion F) => x - 1) ⁻¹'
            {x | Valued.v.restrict x ≤ Valued.v.restrict (((π ^ lev m : F)) : (w.adicCompletion F))}) := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_preimage]
        rw [Valuation.restrict_le_iff, hπv]
      rw [hset]
      exact hc'
    exact hclosed.mem_of_tendsto hL (Filter.Eventually.of_forall fun k => valued_P_sub_one E F w lev ℓ m hstep y₀ hy₀ hy₀1 hy₀fix hmono k)
  refine ⟨L, hL1, hLm, ?_⟩

  have h1 : Tendsto (fun k => cnorm E F w (P E F w lev ℓ m hstep y₀ hy₀ hy₀1 hy₀fix k)) atTop (𝓝 (cnorm E F w L)) :=
    ((continuous_cnorm E F w).tendsto L).comp hL
  have hY : Tendsto (fun k => (Y E F w lev ℓ m hstep y₀ hy₀ hy₀1 hy₀fix k).1) atTop (𝓝 1) := by
    refine tendsto_of_valued_sub_le F w _ 1 0 fun k _ => ?_
    exact (Y E F w lev ℓ m hstep y₀ hy₀ hy₀1 hy₀fix k).2.2.1.trans (WithZero.exp_le_exp.mpr (neg_le_neg (by
      have : k ≤ ℓ * (m + k) := (Nat.le_add_left k m).trans (Nat.le_mul_of_pos_left _ hℓ)
      exact_mod_cast this)))
  have hYinv : Tendsto (fun k => ((Y E F w lev ℓ m hstep y₀ hy₀ hy₀1 hy₀fix k).1)⁻¹) atTop (𝓝 1) := by
    have := hY.inv₀ one_ne_zero
    rwa [inv_one] at this
  have h2 : Tendsto (fun k => cnorm E F w (P E F w lev ℓ m hstep y₀ hy₀ hy₀1 hy₀fix k)) atTop (𝓝 y₀) := by
    have h3 : (fun k => cnorm E F w (P E F w lev ℓ m hstep y₀ hy₀ hy₀1 hy₀fix k)) = fun k => y₀ * ((Y E F w lev ℓ m hstep y₀ hy₀ hy₀1 hy₀fix k).1)⁻¹ := by
      funext k
      have hYk0 : (Y E F w lev ℓ m hstep y₀ hy₀ hy₀1 hy₀fix k).1 ≠ 0 := fun h => by
        have := (Y E F w lev ℓ m hstep y₀ hy₀ hy₀1 hy₀fix k).2.1; rw [h, map_zero] at this; exact zero_ne_one this
      rw [eq_mul_inv_iff_mul_eq₀ hYk0]
      exact (y₀_eq E F w lev ℓ m hstep y₀ hy₀ hy₀1 hy₀fix k).symm
    rw [h3]
    simpa using hYinv.const_mul y₀
  exact tendsto_nhds_unique h1 h2

end lim2
p2m_reactivate "P2MW.S_NumberField_PlaceDecomp_exists_finprod_smul_eq_of_valuation_sub_one_le_of_jump_lt_of_prime_card_decomp.Ws45 P2MW.S_NumberField_PlaceDecomp_exists_finprod_smul_eq_of_valuation_sub_one_le_of_jump_lt_of_prime_card_decomp.Ws45.CL2"

end NumberField.PlaceDecomp.XCSurjLim
p2m_reactivate "P2MW.S_NumberField_PlaceDecomp_exists_finprod_smul_eq_of_valuation_sub_one_le_of_jump_lt_of_prime_card_decomp.Ws45 P2MW.S_NumberField_PlaceDecomp_exists_finprod_smul_eq_of_valuation_sub_one_le_of_jump_lt_of_prime_card_decomp.Ws45.CL2"
p2m_reactivate "P2MW.S_NumberField_PlaceDecomp_exists_finprod_smul_eq_of_valuation_sub_one_le_of_jump_lt_of_prime_card_decomp.Ws45 P2MW.S_NumberField_PlaceDecomp_exists_finprod_smul_eq_of_valuation_sub_one_le_of_jump_lt_of_prime_card_decomp.Ws45.CL2"
p2m_reactivate "P2MW.S_NumberField_PlaceDecomp_exists_finprod_smul_eq_of_valuation_sub_one_le_of_jump_lt_of_prime_card_decomp.Ws45 P2MW.S_NumberField_PlaceDecomp_exists_finprod_smul_eq_of_valuation_sub_one_le_of_jump_lt_of_prime_card_decomp.Ws45.CL2"

open NumberField.PlaceDecomp.XCNormL6 NumberField.PlaceDecomp.XCSurjLim IsDedekindDomain.HeightOneSpectrum in
theorem solution
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (v : HeightOneSpectrum (𝓞 E)) (w : HeightOneSpectrum (𝓞 F)) (hw : w.under (𝓞 E) = v)
    (hℓ : (Nat.card ↥(NumberField.PlaceDecomp.decomp E F w)).Prime)
    (t : ℕ)
    (ht : ((w.valuation F).valuationSubring).lowerRamificationGroup E t = ⊤)
    (ht' : ((w.valuation F).valuationSubring).lowerRamificationGroup E (t + 1) = ⊥)
    (n : ℕ) (hn : t < n) (a : (v.adicCompletion E)ˣ)
    (ha1 : Valued.v (a : v.adicCompletion E) = 1)
    (han : Valued.v ((a : v.adicCompletion E) - 1) ≤ WithZero.exp (-(n : ℤ))) :
    ∃ b : (w.adicCompletion F)ˣ, Valued.v (b : w.adicCompletion F) = 1 ∧
      Valued.v ((b : w.adicCompletion F) - 1) ≤
        WithZero.exp (-((t + Nat.card ↥(NumberField.PlaceDecomp.decomp E F w) * (n - t) : ℕ) : ℤ)) ∧
      (((∏ᶠ σ : ↥(NumberField.PlaceDecomp.decomp E F w), σ • b : (w.adicCompletion F)ˣ) : (w.adicCompletion F)ˣ) : w.adicCompletion F) =
        IsDedekindDomain.HeightOneSpectrum.Extension.adicCompletionSemialgHom E F (⟨w, hw⟩ : v.Extension (𝓞 F)) (a : v.adicCompletion E) := by
  classical
  subst hw
  haveI : Fintype ↥(NumberField.PlaceDecomp.decomp E F w) := Fintype.ofFinite _
  haveI := Ws45.XCL6.faithfulSMul_decomp_valuationSubring E F w
  haveI := Ws45.XCL6.liesOver_maximalIdeal_fixedPoints E F w
  haveI := Ws45.XCL6.isSeparable_residue_fixedPoints E F w
  have hℓ0 : Nat.card ↥(NumberField.PlaceDecomp.decomp E F w) ≠ 0 := hℓ.ne_zero
  have hℓ1 : 1 ≤ Nat.card ↥(NumberField.PlaceDecomp.decomp E F w) := hℓ.one_lt.le
  have hιv := Ws45.XCL6.valued_adicCompletionSemialgHom_eq_pow_natCard E F w (w.under (𝓞 E)) rfl t ht

  have hstep : ∀ k, n ≤ k → ∀ y : (w.adicCompletion F), Valued.v y = 1 →
      Valued.v (y - 1) ≤ WithZero.exp (-((Nat.card ↥(NumberField.PlaceDecomp.decomp E F w) * k : ℕ) : ℤ)) →
      (∀ τ : ↥(NumberField.PlaceDecomp.decomp E F w), τ • y = y) →
      ∃ u : (w.adicCompletion F), Valued.v u = 1 ∧
        Valued.v (u - 1) ≤ WithZero.exp (-((t + Nat.card ↥(NumberField.PlaceDecomp.decomp E F w) * (k - t) : ℕ) : ℤ)) ∧
        Valued.v (cnorm E F w u - y) ≤ WithZero.exp (-((Nat.card ↥(NumberField.PlaceDecomp.decomp E F w) * (k + 1) : ℕ) : ℤ)) := by
    intro k hk y hy1 hyk hyfix
    have htk : t < k := hn.trans_le hk

    obtain ⟨a', ha'⟩ := (NumberField.PlaceDecomp.forall_smul_eq_iff_mem_range_adicCompletionSemialgHom E F w y).mp hyfix

    obtain ⟨e, he⟩ := exists_valued_sub_coe_le E (w.under (𝓞 E)) a' (k + 1)

    set a'' : F := algebraMap E F e with ha''
    have hιe : Extension.adicCompletionSemialgHom E F (⟨w, rfl⟩ : (w.under (𝓞 E)).Extension (𝓞 F))
        ((e : (w.under (𝓞 E)).adicCompletion E)) = (a'' : w.adicCompletion F) :=
      Extension.adicCompletionSemialgHom_coe E F (⟨w, rfl⟩ : (w.under (𝓞 E)).Extension (𝓞 F))
        ((WithVal.equiv ((w.under (𝓞 E)).valuation E)).symm e)

    have hya'' : Valued.v (y - (a'' : w.adicCompletion F)) ≤ WithZero.exp (-((Nat.card ↥(NumberField.PlaceDecomp.decomp E F w) * (k + 1) : ℕ) : ℤ)) := by
      rw [← ha', ← hιe, ← map_sub, hιv,
        show -((Nat.card ↥(NumberField.PlaceDecomp.decomp E F w) * (k + 1) : ℕ) : ℤ) =
          Nat.card ↥(NumberField.PlaceDecomp.decomp E F w) • (-((k + 1 : ℕ) : ℤ)) by push_cast; ring,
        WithZero.exp_nsmul]
      exact pow_le_pow_left₀ zero_le' he _
    have hlt1 : WithZero.exp (-((Nat.card ↥(NumberField.PlaceDecomp.decomp E F w) * (k + 1) : ℕ) : ℤ)) < 1 := by
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
      have : 0 < Nat.card ↥(NumberField.PlaceDecomp.decomp E F w) * (k + 1) := Nat.mul_pos (Nat.pos_of_ne_zero hℓ0) (Nat.succ_pos k)
      omega

    have hva'' : Valued.v (a'' : w.adicCompletion F) = 1 := by
      rw [← hy1]; apply Valuation.map_eq_of_sub_lt; rw [hy1, Valuation.map_sub_swap]; exact lt_of_le_of_lt hya'' hlt1
    have ha''B : a'' ∈ (w.valuation F).valuationSubring := by
      rw [Valuation.mem_valuationSubring_iff, ← valued_coe, hva'']
    have ha''fix : ∀ σ : ↥(NumberField.PlaceDecomp.decomp E F w), σ • (⟨a'', ha''B⟩ : ↥((w.valuation F).valuationSubring)) = ⟨a'', ha''B⟩ := fun σ =>
      Subtype.ext (show (σ : F ≃ₐ[E] F) a'' = a'' from (σ : F ≃ₐ[E] F).commutes e)
    set aA : FixedPoints.subring ↥((w.valuation F).valuationSubring) ↥(NumberField.PlaceDecomp.decomp E F w) := ⟨⟨a'', ha''B⟩, ha''fix⟩ with haA
    have haA1 : ((aA : ↥((w.valuation F).valuationSubring)) : ↥((w.valuation F).valuationSubring)) - 1 ∈ IsLocalRing.maximalIdeal ↥((w.valuation F).valuationSubring) ^ (Nat.card ↥(NumberField.PlaceDecomp.decomp E F w) * k) := by
      rw [mem_maximalIdeal_pow_iff]
      show w.valuation F (a'' - 1) ≤ _
      rw [← valued_coe, coe_sub, coe_one']
      calc Valued.v ((a'' : w.adicCompletion F) - 1)
          = Valued.v (((a'' : w.adicCompletion F) - y) + (y - 1)) := by rw [sub_add_sub_cancel]
        _ ≤ max (Valued.v ((a'' : w.adicCompletion F) - y)) (Valued.v (y - 1)) := Valuation.map_add _ _ _
        _ ≤ WithZero.exp (-((Nat.card ↥(NumberField.PlaceDecomp.decomp E F w) * k : ℕ) : ℤ)) := by
            refine max_le ?_ hyk
            rw [Valuation.map_sub_swap]
            exact hya''.trans (WithZero.exp_le_exp.mpr (neg_le_neg (by exact_mod_cast Nat.mul_le_mul_left _ (Nat.le_succ k))))

    obtain ⟨b', hb'1, hb'N⟩ :=
      IsDiscreteValuationRing.exists_sub_one_mem_and_finprod_smul_sub_mem_of_jump_lt_of_prime_card
        (B := ↥((w.valuation F).valuationSubring)) (G := ↥(NumberField.PlaceDecomp.decomp E F w)) hℓ t ht ht' k htk aA haA1
    refine ⟨((b' : F) : w.adicCompletion F), ?_, ?_, ?_⟩
    ·
      have hlev1 : 1 ≤ t + Nat.card ↥(NumberField.PlaceDecomp.decomp E F w) * (k - t) := by
        have : 1 ≤ Nat.card ↥(NumberField.PlaceDecomp.decomp E F w) * (k - t) := Nat.mul_pos (Nat.pos_of_ne_zero hℓ0) (by omega); omega
      have h := (mem_maximalIdeal_pow_iff F w _ _).mp hb'1
      have h' : Valued.v (((b' : F) : w.adicCompletion F) - 1) < 1 := by
        rw [← coe_one', ← coe_sub, valued_coe]
        refine lt_of_le_of_lt h ?_
        rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
      rw [show ((b' : F) : w.adicCompletion F) = 1 + (((b' : F) : w.adicCompletion F) - 1) by ring]
      exact Valuation.map_one_add_of_lt _ h'
    · rw [← coe_one', ← coe_sub, valued_coe]
      exact (mem_maximalIdeal_pow_iff F w _ _).mp hb'1
    ·
      have hNb' : cnorm E F w ((b' : F) : w.adicCompletion F) = ((((∏ᶠ σ : ↥(NumberField.PlaceDecomp.decomp E F w), σ • b' : ↥((w.valuation F).valuationSubring)) : F)) : w.adicCompletion F) := by
        rw [cnorm_def, finprod_eq_prod_of_fintype, SubmonoidClass.coe_finsetProd, coe_prod]
        exact Finset.prod_congr rfl fun σ _ => smul_coe E F w σ (b' : F)
      have hdiff : Valued.v (cnorm E F w ((b' : F) : w.adicCompletion F) - (a'' : w.adicCompletion F)) ≤
          WithZero.exp (-((Nat.card ↥(NumberField.PlaceDecomp.decomp E F w) * (k + 1) : ℕ) : ℤ)) := by
        have h := (mem_maximalIdeal_pow_iff F w _ _).mp hb'N
        rw [hNb', ← coe_sub, valued_coe]
        exact h
      calc Valued.v (cnorm E F w ((b' : F) : w.adicCompletion F) - y)
          = Valued.v ((cnorm E F w ((b' : F) : w.adicCompletion F) - (a'' : w.adicCompletion F)) + ((a'' : w.adicCompletion F) - y)) := by
            rw [sub_add_sub_cancel]
        _ ≤ _ := Valuation.map_add _ _ _
        _ ≤ WithZero.exp (-((Nat.card ↥(NumberField.PlaceDecomp.decomp E F w) * (k + 1) : ℕ) : ℤ)) := max_le hdiff (by rw [Valuation.map_sub_swap]; exact hya'')

  set y₀ : w.adicCompletion F := Extension.adicCompletionSemialgHom E F (⟨w, rfl⟩ : (w.under (𝓞 E)).Extension (𝓞 F))
    (a : (w.under (𝓞 E)).adicCompletion E) with hy₀def
  have hy₀fix : ∀ τ : ↥(NumberField.PlaceDecomp.decomp E F w), τ • y₀ = y₀ :=
    (NumberField.PlaceDecomp.forall_smul_eq_iff_mem_range_adicCompletionSemialgHom E F w y₀).mpr ⟨_, rfl⟩
  have hy₀ : Valued.v y₀ = 1 := by rw [hy₀def, hιv, ha1, one_pow]
  have hy₀1 : Valued.v (y₀ - 1) ≤ WithZero.exp (-((Nat.card ↥(NumberField.PlaceDecomp.decomp E F w) * n : ℕ) : ℤ)) := by
    rw [hy₀def, ← map_one (Extension.adicCompletionSemialgHom E F (⟨w, rfl⟩ : (w.under (𝓞 E)).Extension (𝓞 F))),
      ← map_sub, hιv,
      show -((Nat.card ↥(NumberField.PlaceDecomp.decomp E F w) * n : ℕ) : ℤ) =
        Nat.card ↥(NumberField.PlaceDecomp.decomp E F w) • (-(n : ℤ)) by push_cast; ring,
      WithZero.exp_nsmul]
    exact pow_le_pow_left₀ zero_le' han _

  obtain ⟨b, hb1, hbm, hNb⟩ := exists_cnorm_eq E F w (fun k => t + Nat.card ↥(NumberField.PlaceDecomp.decomp E F w) * (k - t)) (Nat.card ↥(NumberField.PlaceDecomp.decomp E F w)) n
    hstep y₀ hy₀ hy₀1 hy₀fix
    (fun k => by
      have : k - t ≤ Nat.card ↥(NumberField.PlaceDecomp.decomp E F w) * (k - t) := Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hℓ0)
      beta_reduce; omega)
    (fun k k' hkk' => by dsimp only; exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.sub_le_sub_right hkk' t)) t)
    hℓ1
  have hb0 : b ≠ 0 := fun h => by rw [h, map_zero] at hb1; exact zero_ne_one hb1
  refine ⟨Units.mk0 b hb0, hb1, hbm, ?_⟩
  rw [← hNb, cnorm_def, finprod_eq_prod_of_fintype, Units.coe_prod]
  exact Finset.prod_congr rfl fun σ _ => NumberField.PlaceDecomp.coe_smul_units σ (Units.mk0 b hb0)

end S_NumberField_PlaceDecomp_exists_finprod_smul_eq_of_valuation_sub_one_le_of_jump_lt_of_prime_card_decomp
end P2MW
export P2MW.S_NumberField_PlaceDecomp_exists_finprod_smul_eq_of_valuation_sub_one_le_of_jump_lt_of_prime_card_decomp (solution)
