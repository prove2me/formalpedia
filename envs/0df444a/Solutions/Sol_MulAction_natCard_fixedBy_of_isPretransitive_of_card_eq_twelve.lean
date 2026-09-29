-- Prove2me | solution 1 for MulAction.natCard_fixedBy_of_isPretransitive_of_card_eq_twelve
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/d7a7b417-22a9-58c1-ae61-739c9e5195f0

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MulAction_natCard_fixedBy_of_isPretransitive_of_card_eq_twelve

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace P2MKcMarksA4

open MulAction Subgroup

variable {G : Type*} [Group G] [Finite G]

scoped instance fact_prime_two' : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
scoped instance fact_prime_three' : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

theorem factorization_twelve_three : (12 : ℕ).factorization 3 = 1 := by
  rw [Nat.factorization_def _ Nat.prime_three]
  have : (12 : ℕ) = 3 ^ 1 * 4 := by norm_num
  rw [this, padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd (by norm_num)]

theorem factorization_twelve_two : (12 : ℕ).factorization 2 = 2 := by
  rw [Nat.factorization_def _ Nat.prime_two]
  have : (12 : ℕ) = 2 ^ 2 * 3 := by norm_num
  rw [this, padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd (by norm_num)]

section Structure

variable (hG : Nat.card G = 12) (hexp : ∀ g : G, g ^ 2 = 1 ∨ g ^ 3 = 1)

include hexp in
theorem orderOf_cases (g : G) : orderOf g = 1 ∨ orderOf g = 2 ∨ orderOf g = 3 := by
  rcases hexp g with h | h
  · have hd := orderOf_dvd_of_pow_eq_one h
    have := Nat.le_of_dvd (by norm_num) hd
    interval_cases (orderOf g) <;> simp_all
  · have hd := orderOf_dvd_of_pow_eq_one h
    have := Nat.le_of_dvd (by norm_num) hd
    interval_cases (orderOf g) <;> simp_all

include hexp in

theorem not_commute {a b : G} (ha : orderOf a = 2) (hb : orderOf b = 3) : ¬Commute a b := by
  intro h
  have h6 : orderOf (a * b) = 6 := by
    rw [h.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [ha, hb]; norm_num), ha, hb]
  rcases orderOf_cases hexp (a * b) with h1 | h1 | h1 <;> omega

theorem orderOf_eq_two_of_sq {a : G} (ha : a ^ 2 = 1) (ha1 : a ≠ 1) : orderOf a = 2 :=
  orderOf_eq_prime ha ha1

theorem orderOf_eq_three_of_cube {b : G} (hb : b ^ 3 = 1) (hb1 : b ≠ 1) : orderOf b = 3 :=
  orderOf_eq_prime hb hb1

include hexp in
theorem sq_eq_one_of_orderOf_ne_three {g : G} (h : orderOf g ≠ 3) : g ^ 2 = 1 := by
  rcases orderOf_cases hexp g with h1 | h1 | h1
  · rw [orderOf_eq_one_iff.mp h1, one_pow]
  · rw [← h1, pow_orderOf_eq_one]
  · exact absurd h1 h

include hG in
theorem card_sylow_three (P : Sylow 3 G) : Nat.card (P : Subgroup G) = 3 := by
  rw [Sylow.card_eq_multiplicity, hG, factorization_twelve_three, pow_one]

include hG in
theorem card_sylow_two (Q : Sylow 2 G) : Nat.card (Q : Subgroup G) = 4 := by
  rw [Sylow.card_eq_multiplicity, hG, factorization_twelve_two]; norm_num

theorem orderOf_eq_three_of_mem {H : Subgroup G} (hH : Nat.card H = 3) {g : G} (hg : g ∈ H)
    (hg1 : g ≠ 1) : orderOf g = 3 := by
  have hd : orderOf g ∣ 3 := hH ▸ Subgroup.orderOf_dvd_natCard H hg
  rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h
  · exact absurd (orderOf_eq_one_iff.mp h) hg1
  · exact h

theorem zpowers_eq_of_mem {H : Subgroup G} (hH : Nat.card H = 3) {g : G} (hg : g ∈ H) (hg1 : g ≠ 1) :
    Subgroup.zpowers g = H := by
  haveI : Finite H := Nat.finite_of_card_ne_zero (by rw [hH]; norm_num)
  apply Subgroup.eq_of_le_of_card_ge
  · rw [Subgroup.zpowers_le]; exact hg
  · rw [hH, Nat.card_zpowers, orderOf_eq_three_of_mem hH hg hg1]

theorem mem_of_card_three {H : Subgroup G} (hH : Nat.card H = 3) {c : G} (hc : c ∈ H) (hc1 : c ≠ 1)
    {g : G} (hg : g ∈ H) : g = 1 ∨ g = c ∨ g = c ^ 2 := by
  have hoc := orderOf_eq_three_of_mem hH hc hc1
  rw [← zpowers_eq_of_mem hH hc hc1, Subgroup.mem_zpowers_iff] at hg
  obtain ⟨k, rfl⟩ := hg
  rw [← zpow_mod_orderOf, hoc]
  have h0 : 0 ≤ k % 3 := Int.emod_nonneg k (by norm_num)
  have h3 : k % 3 < 3 := Int.emod_lt_of_pos k (by norm_num)
  interval_cases (k % 3)
  · left; simp
  · right; left; simp
  · right; right; norm_cast

include hG hexp in

theorem sylow_three_not_normal (P : Sylow 3 G) : ¬(P : Subgroup G).Normal := by
  intro hn
  have hP := card_sylow_three hG P

  haveI : Finite (P : Subgroup G) := Nat.finite_of_card_ne_zero (by rw [hP]; norm_num)
  obtain ⟨⟨c, hcP⟩, hc1⟩ : ∃ c : (P : Subgroup G), c ≠ 1 := by
    by_contra h
    push Not at h
    have : Nat.card (P : Subgroup G) ≤ 1 := by
      rw [Finite.card_le_one_iff_subsingleton]
      exact ⟨fun a b => by rw [h a, h b]⟩
    omega
  have hc1 : c ≠ 1 := fun h => hc1 (Subtype.ext h)
  have hoc : orderOf c = 3 := orderOf_eq_three_of_mem hP hcP hc1

  have hconj : ∀ x : G, x * c * x⁻¹ = c ∨ x * c * x⁻¹ = c ^ 2 := by
    intro x
    have hm : x * c * x⁻¹ ∈ (P : Subgroup G) := hn.conj_mem c hcP x
    rcases mem_of_card_three hP hcP hc1 hm with h | h | h
    · exfalso; apply hc1
      have : c = x⁻¹ * (x * c * x⁻¹) * x := by group
      rw [this, h]; group
    · exact Or.inl h
    · exact Or.inr h

  obtain ⟨Q⟩ : Nonempty (Sylow 2 G) := inferInstance
  have hQ := card_sylow_two hG Q
  haveI : Finite (Q : Subgroup G) := Nat.finite_of_card_ne_zero (by rw [hQ]; norm_num)
  have hQexp : ∀ q : G, q ∈ (Q : Subgroup G) → q ^ 2 = 1 := by
    intro q hq
    apply sq_eq_one_of_orderOf_ne_three hexp
    intro h3
    have : orderOf q ∣ 4 := hQ ▸ Subgroup.orderOf_dvd_natCard (Q : Subgroup G) hq
    rw [h3] at this; norm_num at this
  obtain ⟨q₁, hq₁Q, hq₁⟩ : ∃ q₁ : G, q₁ ∈ (Q : Subgroup G) ∧ q₁ ≠ 1 := by
    by_contra h; push Not at h
    have : Nat.card (Q : Subgroup G) ≤ 1 := by
      rw [Finite.card_le_one_iff_subsingleton]
      exact ⟨fun a b => Subtype.ext (by rw [h a a.2, h b b.2])⟩
    omega
  obtain ⟨q₂, hq₂Q, hq₂, hq₂₁⟩ : ∃ q₂ : G, q₂ ∈ (Q : Subgroup G) ∧ q₂ ≠ 1 ∧ q₂ ≠ q₁ := by
    by_contra h; push Not at h
    have : Nat.card (Q : Subgroup G) ≤ 2 := by
      let f : Bool → (Q : Subgroup G) := fun b => if b then ⟨q₁, hq₁Q⟩ else 1
      have hf : Function.Surjective f := by
        rintro ⟨q, hq⟩
        by_cases hq1 : q = 1
        · exact ⟨false, Subtype.ext (by simp [f, hq1])⟩
        · exact ⟨true, Subtype.ext (by simp [f, (h q hq hq1)])⟩
      simpa using Nat.card_le_card_of_surjective f hf
    omega

  have hcomm : ∃ q : G, q ∈ (Q : Subgroup G) ∧ q ≠ 1 ∧ q * c * q⁻¹ = c := by
    rcases hconj q₁ with h1 | h1
    · exact ⟨q₁, hq₁Q, hq₁, h1⟩
    rcases hconj q₂ with h2 | h2
    · exact ⟨q₂, hq₂Q, hq₂, h2⟩
    refine ⟨q₁ * q₂, (Q : Subgroup G).mul_mem hq₁Q hq₂Q, ?_, ?_⟩
    · intro h
      apply hq₂₁
      have hq1sq := hQexp q₁ hq₁Q
      calc q₂ = q₁ ^ 2 * q₂ := by rw [hq1sq, one_mul]
        _ = q₁ * (q₁ * q₂) := by rw [sq, mul_assoc]
        _ = q₁ := by rw [h, mul_one]
    · have hc3 : c ^ 3 = 1 := by rw [← hoc]; exact pow_orderOf_eq_one c
      calc q₁ * q₂ * c * (q₁ * q₂)⁻¹ = q₁ * (q₂ * c * q₂⁻¹) * q₁⁻¹ := by group
        _ = q₁ * c ^ 2 * q₁⁻¹ := by rw [h2]
        _ = (q₁ * c * q₁⁻¹) ^ 2 := by simp only [sq]; group
        _ = (c ^ 2) ^ 2 := by rw [h1]
        _ = c * c ^ 3 := by simp only [sq, pow_succ, pow_zero, one_mul, mul_assoc]
        _ = c := by rw [hc3, mul_one]
  obtain ⟨q, hqQ, hq1, hqc⟩ := hcomm
  have hoq : orderOf q = 2 := orderOf_eq_two_of_sq (hQexp q hqQ) hq1
  exact not_commute hexp hoq hoc (by
    rw [commute_iff_eq]
    calc q * c = q * c * q⁻¹ * q := by group
      _ = c * q := by rw [hqc])

end Structure

section Structure2

variable (hG : Nat.card G = 12) (hexp : ∀ g : G, g ^ 2 = 1 ∨ g ^ 3 = 1)
include hG hexp

theorem card_sylow_three_eq_four : Nat.card (Sylow 3 G) = 4 := by
  obtain ⟨P⟩ : Nonempty (Sylow 3 G) := inferInstance
  have h1 : Nat.card (Sylow 3 G) ≡ 1 [MOD 3] := card_sylow_modEq_one 3 G
  have h2 : Nat.card (Sylow 3 G) ∣ (P : Subgroup G).index := P.card_dvd_index
  have hidx : (P : Subgroup G).index = 4 := by
    have := (P : Subgroup G).index_mul_card
    rw [hG, card_sylow_three hG P] at this
    omega
  rw [hidx] at h2
  have hne : Nat.card (Sylow 3 G) ≠ 1 := by
    intro h
    apply sylow_three_not_normal hG hexp P
    have h' := Sylow.card_eq_index_normalizer P
    rw [h] at h'
    exact Subgroup.normalizer_eq_top_iff.mp (Subgroup.index_eq_one.mp h'.symm)
  have hle : Nat.card (Sylow 3 G) ≤ 4 := Nat.le_of_dvd (by norm_num) h2
  interval_cases h : (Nat.card (Sylow 3 G))
  · norm_num at h2
  · exact absurd rfl hne
  · exact absurd h1 (by decide)
  · norm_num at h2
  · rfl

omit hG hexp in
theorem exists_sylow_mem_of_orderOf {g : G} (hg : orderOf g = 3) : ∃ P : Sylow 3 G, g ∈ (P : Subgroup G) := by
  have : IsPGroup 3 (Subgroup.zpowers g) := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hg, pow_one])
  obtain ⟨P, hP⟩ := this.exists_le_sylow
  exact ⟨P, hP (Subgroup.mem_zpowers g)⟩

omit hexp in
theorem sylow_eq_of_mem {g : G} (hg1 : g ≠ 1) {P P' : Sylow 3 G} (h : g ∈ (P : Subgroup G))
    (h' : g ∈ (P' : Subgroup G)) : P = P' := by
  apply Sylow.ext
  rw [← zpowers_eq_of_mem (card_sylow_three hG P) h hg1, ← zpowers_eq_of_mem (card_sylow_three hG P') h' hg1]

omit hG hexp in
theorem heq_subtype_of_sylow_eq {P₁ P₂ : Sylow 3 G} (h : P₁ = P₂) {g : G}
    (h₁ : g ∈ (P₁ : Subgroup G) ∧ g ≠ 1) (h₂ : g ∈ (P₂ : Subgroup G) ∧ g ≠ 1) :
    HEq (⟨g, h₁⟩ : {g : G // g ∈ (P₁ : Subgroup G) ∧ g ≠ 1})
      (⟨g, h₂⟩ : {g : G // g ∈ (P₂ : Subgroup G) ∧ g ≠ 1}) := by
  subst h; rfl

theorem ncard_orderOf_eq_three : {g : G | orderOf g = 3}.ncard = 8 := by
  classical
  letI : Fintype (Sylow 3 G) := Fintype.ofFinite _
  have hne : ∀ {g : G}, orderOf g = 3 → g ≠ 1 := by
    intro g hg h; rw [h, orderOf_one] at hg; norm_num at hg
  let Pof : {g : G | orderOf g = 3} → Sylow 3 G := fun g => (exists_sylow_mem_of_orderOf g.2).choose
  have hPof : ∀ g : {g : G | orderOf g = 3}, (g : G) ∈ (Pof g : Subgroup G) := fun g =>
    (exists_sylow_mem_of_orderOf g.2).choose_spec
  have e : {g : G | orderOf g = 3} ≃ Σ P : Sylow 3 G, {g : G // g ∈ (P : Subgroup G) ∧ g ≠ 1} :=
    { toFun := fun g => ⟨Pof g, ⟨g.1, hPof g, hne g.2⟩⟩
      invFun := fun x => ⟨x.2.1, orderOf_eq_three_of_mem (card_sylow_three hG x.1) x.2.2.1 x.2.2.2⟩
      left_inv := fun g => Subtype.ext rfl
      right_inv := by
        rintro ⟨P, g, hgP, hg1⟩
        have hP : Pof ⟨g, orderOf_eq_three_of_mem (card_sylow_three hG P) hgP hg1⟩ = P :=
          sylow_eq_of_mem hG hg1 (hPof _) hgP
        exact Sigma.ext hP (heq_subtype_of_sylow_eq hP _ _) }
  have h2 : ∀ P : Sylow 3 G, Nat.card {g : G // g ∈ (P : Subgroup G) ∧ g ≠ 1} = 2 := by
    intro P
    have hs : {g : G | g ∈ (P : Subgroup G) ∧ g ≠ 1} = ((P : Subgroup G) : Set G) \ {1} := by
      ext g
      simp only [Set.mem_setOf_eq, Set.mem_diff, SetLike.mem_coe, Set.mem_singleton_iff]
    have h3 : (((P : Subgroup G) : Set G)).ncard = 3 := by
      rw [← Nat.card_coe_set_eq]; exact card_sylow_three hG P
    have := Set.ncard_diff_singleton_of_mem (show (1 : G) ∈ ((P : Subgroup G) : Set G) from
      (P : Subgroup G).one_mem)
    rw [h3] at this
    change Nat.card ({g : G | g ∈ (P : Subgroup G) ∧ g ≠ 1} : Set G) = 2
    rw [Nat.card_coe_set_eq, hs, this]
  rw [← Nat.card_coe_set_eq, Nat.card_congr e, Nat.card_sigma]
  simp only [h2, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [← Nat.card_eq_fintype_card, card_sylow_three_eq_four hG hexp]

theorem ncard_sq_eq_one : {g : G | g ^ 2 = 1}.ncard = 4 := by
  have hunion : {g : G | g ^ 2 = 1} ∪ {g | orderOf g = 3} = Set.univ := by
    ext g
    simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    by_cases h : orderOf g = 3
    · exact Or.inr h
    · exact Or.inl (sq_eq_one_of_orderOf_ne_three hexp h)
  have hdisj : Disjoint {g : G | g ^ 2 = 1} {g | orderOf g = 3} := by
    rw [Set.disjoint_left]
    intro g h1 h2
    have := orderOf_dvd_of_pow_eq_one h1
    rw [h2] at this
    norm_num at this
  have h := Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)
  rw [hunion, Set.ncard_univ, hG, ncard_orderOf_eq_three hG hexp] at h
  omega

theorem mem_iff_sq_eq_one_of_card_eq_four {H : Subgroup G} (hH : Nat.card H = 4) (g : G) :
    g ∈ H ↔ g ^ 2 = 1 := by
  have hsub : (H : Set G) ⊆ {g : G | g ^ 2 = 1} := by
    intro h hh
    apply sq_eq_one_of_orderOf_ne_three hexp
    intro h3
    have : orderOf h ∣ 4 := hH ▸ Subgroup.orderOf_dvd_natCard H hh
    rw [h3] at this; norm_num at this
  have heq : (H : Set G) = {g : G | g ^ 2 = 1} :=
    Set.eq_of_subset_of_ncard_le hsub (by
      rw [ncard_sq_eq_one hG hexp, ← Nat.card_coe_set_eq]
      exact hH.symm.le) (Set.toFinite _)
  rw [← SetLike.mem_coe, heq]; rfl

theorem sq_mul_eq_one {x y : G} (hx : x ^ 2 = 1) (hy : y ^ 2 = 1) : (x * y) ^ 2 = 1 := by
  obtain ⟨Q⟩ : Nonempty (Sylow 2 G) := inferInstance
  have hQ := card_sylow_two hG Q
  rw [← mem_iff_sq_eq_one_of_card_eq_four hG hexp hQ] at hx hy ⊢
  exact (Q : Subgroup G).mul_mem hx hy

theorem mul_eq_mul_iff_sq_eq_one {a : G} (ha : orderOf a = 2) (x : G) : x * a = a * x ↔ x ^ 2 = 1 := by
  constructor
  · intro h
    apply sq_eq_one_of_orderOf_ne_three hexp
    intro hx
    exact not_commute hexp ha hx h.symm
  · intro hx
    have ha2 : a ^ 2 = 1 := by rw [← ha, pow_orderOf_eq_one]
    have hxa := sq_mul_eq_one hG hexp hx ha2

    have h1 : x * a = (x * a)⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← sq, hxa]
    have h2 : x⁻¹ = x := by rw [inv_eq_iff_mul_eq_one, ← sq, hx]
    have h3 : a⁻¹ = a := by rw [inv_eq_iff_mul_eq_one, ← sq, ha2]
    rw [h1, mul_inv_rev, h2, h3]

theorem exists_conj_eq {a τ : G} (ha : orderOf a = 2) (hτ : orderOf τ = 2) : ∃ x : G, x⁻¹ * a * x = τ := by
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := G) 3 (by rw [hG]; norm_num)
  have hb3 : b ^ 3 = 1 := by rw [← hb, pow_orderOf_eq_one]
  have ha1 : a ≠ 1 := by intro h; rw [h, orderOf_one] at ha; norm_num at ha
  have hτ1 : τ ≠ 1 := by intro h; rw [h, orderOf_one] at hτ; norm_num at hτ
  have ha2 : a ^ 2 = 1 := by rw [← ha, pow_orderOf_eq_one]
  have hτ2 : τ ^ 2 = 1 := by rw [← hτ, pow_orderOf_eq_one]

  set a₁ := b⁻¹ * a * b with ha₁
  set a₂ := (b ^ 2)⁻¹ * a * b ^ 2 with ha₂
  have hb2 : orderOf (b ^ 2) = 3 := by
    apply orderOf_eq_three_of_cube
    · rw [← pow_mul, show 2 * 3 = 3 * 2 by norm_num, pow_mul, hb3, one_pow]
    · intro h
      have : b = 1 := by
        calc b = b ^ 3 * (b ^ 2)⁻¹ := by group
          _ = 1 := by rw [hb3, h]; group
      rw [this, orderOf_one] at hb; norm_num at hb
  have hne01 : a ≠ a₁ := by
    intro h
    apply not_commute hexp ha hb
    rw [commute_iff_eq]
    calc a * b = b * (b⁻¹ * a * b) := by group
      _ = b * a := by rw [← ha₁, ← h]
  have hne02 : a ≠ a₂ := by
    intro h
    apply not_commute hexp ha hb2
    rw [commute_iff_eq]
    calc a * b ^ 2 = b ^ 2 * ((b ^ 2)⁻¹ * a * b ^ 2) := by group
      _ = b ^ 2 * a := by rw [← ha₂, ← h]
  have hne12 : a₁ ≠ a₂ := by
    intro h
    apply hne01
    calc a = b * a₁ * b⁻¹ := by rw [ha₁]; group
      _ = b * a₂ * b⁻¹ := by rw [h]
      _ = a₁ := by rw [ha₂, ha₁]; simp only [sq]; group
  have ha2' : a * a = 1 := by rw [← sq]; exact ha2
  have hsq₁ : a₁ ^ 2 = 1 := by
    rw [ha₁]
    calc (b⁻¹ * a * b) ^ 2 = b⁻¹ * (a * a) * b := by simp only [sq]; group
    _ = 1 := by rw [ha2']; group
  have hsq₂ : a₂ ^ 2 = 1 := by
    rw [ha₂]
    calc ((b ^ 2)⁻¹ * a * b ^ 2) ^ 2 = (b ^ 2)⁻¹ * (a * a) * b ^ 2 := by simp only [sq]; group
    _ = 1 := by rw [ha2']; group
  have h1₁ : a₁ ≠ 1 := by
    intro h; apply ha1
    calc a = b * a₁ * b⁻¹ := by rw [ha₁]; group
      _ = 1 := by rw [h]; group
  have h1₂ : a₂ ≠ 1 := by
    intro h; apply ha1
    calc a = b ^ 2 * a₂ * (b ^ 2)⁻¹ := by rw [ha₂]; group
      _ = 1 := by rw [h]; group

  have hsub : ({1, a, a₁, a₂} : Set G) ⊆ {g : G | g ^ 2 = 1} := by
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · simp
    · exact ha2
    · exact hsq₁
    · exact hsq₂
  have hcard : ({1, a, a₁, a₂} : Set G).ncard = 4 := by
    rw [Set.ncard_insert_of_notMem (by simp [Ne.symm ha1, Ne.symm h1₁, Ne.symm h1₂]),
      Set.ncard_insert_of_notMem (by simp [hne01, hne02]),
      Set.ncard_pair hne12]
  have heq : ({1, a, a₁, a₂} : Set G) = {g : G | g ^ 2 = 1} :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [ncard_sq_eq_one hG hexp, hcard]) (Set.toFinite _)
  have hτmem : τ ∈ ({1, a, a₁, a₂} : Set G) := by rw [heq]; exact hτ2
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hτmem
  rcases hτmem with h | h | h | h
  · exact absurd h hτ1
  · exact ⟨1, by rw [h]; group⟩
  · exact ⟨b, by rw [h, ha₁]⟩
  · exact ⟨b ^ 2, by rw [h, ha₂]⟩

theorem mem_zpowers_of_mul_eq_mul {b x : G} (hb : orderOf b = 3) (h : x * b = b * x) :
    x ∈ Subgroup.zpowers b := by
  set C := Subgroup.centralizer ({b} : Set G) with hC
  have hxC : x ∈ C := by rw [hC, Subgroup.mem_centralizer_singleton_iff]; exact h
  have hbC : b ∈ C := by rw [hC, Subgroup.mem_centralizer_singleton_iff]
  have hpC : IsPGroup 3 C := by
    intro k
    refine ⟨1, ?_⟩
    rw [pow_one]
    have hk : (k : G) * b = b * k := Subgroup.mem_centralizer_singleton_iff.mp k.2
    have hk3 : orderOf (k : G) ≠ 2 := fun h2 => not_commute hexp h2 hb hk
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    rcases orderOf_cases hexp (k : G) with h1 | h1 | h1
    · rw [orderOf_eq_one_iff.mp h1, one_pow]
    · exact absurd h1 hk3
    · rw [← h1, pow_orderOf_eq_one]
  obtain ⟨P, hCP⟩ := hpC.exists_le_sylow
  have hb1 : b ≠ 1 := by intro h1; rw [h1, orderOf_one] at hb; norm_num at hb
  rw [zpowers_eq_of_mem (card_sylow_three hG P) (hCP hbC) hb1]
  exact hCP hxC

theorem conj_ne_sq {c z : G} (hc : orderOf c = 3) : z⁻¹ * c * z ≠ c ^ 2 := by
  intro h
  have hc3 : c ^ 3 = 1 := by rw [← hc, pow_orderOf_eq_one]
  have hc1 : c ≠ 1 := by intro h1; rw [h1, orderOf_one] at hc; norm_num at hc
  have hcc : c ≠ c ^ 2 := by
    intro h2; apply hc1
    have h2' : c * c = c := by rw [← sq]; exact h2.symm
    calc c = c * c * c⁻¹ := by group
      _ = 1 := by rw [h2']; group
  rcases orderOf_cases hexp z with hz | hz | hz
  · rw [orderOf_eq_one_iff.mp hz] at h
    apply hcc; simpa using h
  ·
    have hz2 : z ^ 2 = 1 := by rw [← hz, pow_orderOf_eq_one]
    have hzi : z⁻¹ = z := by rw [inv_eq_iff_mul_eq_one, ← sq, hz2]
    rw [hzi] at h
    have hzc : (z * c) ^ 2 = 1 := by
      calc (z * c) ^ 2 = z * c * z * c := by simp only [sq]; group
        _ = c ^ 2 * c := by rw [h]
        _ = 1 := by rw [← pow_succ, hc3]
    have hc2 : c ^ 2 = 1 := by
      have := sq_mul_eq_one hG hexp hz2 hzc
      calc c ^ 2 = (z * (z * c)) ^ 2 := by rw [← mul_assoc, ← sq, hz2, one_mul]
        _ = 1 := this
    apply hc1
    calc c = c ^ 3 * (c ^ 2)⁻¹ := by group
      _ = 1 := by rw [hc3, hc2]; group
  ·
    have hz3 : z ^ 3 = 1 := by rw [← hz, pow_orderOf_eq_one]
    have h2 : (z ^ 2)⁻¹ * c * z ^ 2 = c := by
      calc (z ^ 2)⁻¹ * c * z ^ 2 = z⁻¹ * (z⁻¹ * c * z) * z := by simp only [sq]; group
        _ = z⁻¹ * c ^ 2 * z := by rw [h]
        _ = (z⁻¹ * c * z) ^ 2 := by simp only [sq]; group
        _ = (c ^ 2) ^ 2 := by rw [h]
        _ = c ^ 3 * c := by simp only [sq, pow_succ, pow_zero, one_mul]; group
        _ = c := by rw [hc3, one_mul]
    have hzz : z ^ 2 = z⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← pow_succ, hz3]
    rw [hzz, inv_inv] at h2

    have : z⁻¹ * c * z = c := by
      calc z⁻¹ * c * z = z⁻¹ * (z * c * z⁻¹) * z := by rw [h2]
        _ = c := by group
    rw [this] at h
    exact hcc h

end Structure2

section Marks

variable (X : Type*) [MulAction G X]

theorem card_fixedBy_mul_card_stabilizer [IsPretransitive G X] (x₀ : X) (g : G) :
    Nat.card (fixedBy X g) * Nat.card (stabilizer G x₀) =
      Nat.card {x : G // x⁻¹ * g * x ∈ stabilizer G x₀} := by
  classical
  set H := stabilizer G x₀ with hH
  let ψ : G ⧸ H → X := fun q => ((orbitEquivQuotientStabilizer G x₀).symm q : orbit G x₀)
  have hψ : ∀ a : G, ψ (a : G ⧸ H) = a • x₀ := fun a => orbitEquivQuotientStabilizer_symm_apply G x₀ a
  have hψinj : Function.Injective ψ := Subtype.val_injective.comp (Equiv.injective _)
  have hψsurj : Function.Surjective ψ := by
    intro x
    obtain ⟨a, ha⟩ := exists_smul_eq G x₀ x
    exact ⟨a, by rw [hψ, ha]⟩
  have e1 : fixedBy X g ≃ fixedBy (G ⧸ H) g := by
    refine ((Equiv.ofBijective ψ ⟨hψinj, hψsurj⟩).subtypeEquiv ?_).symm
    intro q
    induction q using QuotientGroup.induction_on with
    | H a =>
      show g • (a : G ⧸ H) = (a : G ⧸ H) ↔ g • ψ (a : G ⧸ H) = ψ (a : G ⧸ H)
      rw [MulAction.Quotient.smul_coe, smul_eq_mul, hψ, ← mul_smul, ← hψ, ← hψ, hψinj.eq_iff]
  have e2 : (QuotientGroup.mk ⁻¹' fixedBy (G ⧸ H) g : Set G) = {x : G | x⁻¹ * g * x ∈ H} := by
    ext a
    simp only [Set.mem_preimage, mem_fixedBy, Set.mem_setOf_eq, MulAction.Quotient.smul_coe,
      QuotientGroup.eq]
    rw [smul_eq_mul, show (g * a)⁻¹ * a = (a⁻¹ * g * a)⁻¹ by group, H.inv_mem_iff]
  calc Nat.card (fixedBy X g) * Nat.card H = Nat.card H * Nat.card (fixedBy (G ⧸ H) g) := by
        rw [Nat.card_congr e1, mul_comm]
    _ = Nat.card (QuotientGroup.mk ⁻¹' fixedBy (G ⧸ H) g : Set G) :=
        (QuotientGroup.card_preimage_mk H _).symm
    _ = Nat.card {x : G // x⁻¹ * g * x ∈ H} := by rw [e2]; rfl

omit [Finite G] in
theorem mem_smul_sylow_iff (g : G) (P : Sylow 3 G) (x : G) :
    x ∈ ((g • P : Sylow 3 G) : Subgroup G) ↔ g⁻¹ * x * g ∈ (P : Subgroup G) := by
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp [MulAut.smul_def, mul_assoc]

variable (hG : Nat.card G = 12) (hexp : ∀ g : G, g ^ 2 = 1 ∨ g ^ 3 = 1)
variable [Nonempty X] [IsPretransitive G X]
include hG hexp

theorem marks :
    (Nat.card X = 1 ∨ Nat.card X = 3 ∨ Nat.card X = 4 ∨ Nat.card X = 6 ∨ Nat.card X = 12) ∧
    (∀ a : G, a ≠ 1 → a ^ 2 = 1 →
      (Nat.card X = 1 → Nat.card (fixedBy X a) = 1) ∧
      (Nat.card X = 3 → Nat.card (fixedBy X a) = 3) ∧
      (Nat.card X = 4 → Nat.card (fixedBy X a) = 0) ∧
      (Nat.card X = 6 → Nat.card (fixedBy X a) = 2) ∧
      (Nat.card X = 12 → Nat.card (fixedBy X a) = 0)) ∧
    (∀ b : G, b ≠ 1 → b ^ 3 = 1 →
      (Nat.card X = 1 → Nat.card (fixedBy X b) = 1) ∧
      (Nat.card X = 3 → Nat.card (fixedBy X b) = 0) ∧
      (Nat.card X = 4 → Nat.card (fixedBy X b) = 1) ∧
      (Nat.card X = 6 → Nat.card (fixedBy X b) = 0) ∧
      (Nat.card X = 12 → Nat.card (fixedBy X b) = 0)) := by
  classical
  obtain ⟨x₀⟩ := (inferInstance : Nonempty X)
  set H := stabilizer G x₀ with hH
  have hidx : H.index = Nat.card X := index_stabilizer_of_transitive G x₀
  have hHX : Nat.card X * Nat.card H = 12 := by rw [← hidx, H.index_mul_card, hG]
  have hHpos : 0 < Nat.card H := Nat.card_pos
  have hHdvd : Nat.card H ∣ 12 := hG ▸ Subgroup.card_subgroup_dvd_card H

  have key : ∀ g : G, Nat.card (fixedBy X g) * Nat.card H = Nat.card {x : G // x⁻¹ * g * x ∈ H} :=
    card_fixedBy_mul_card_stabilizer X x₀

  have hH6 : Nat.card H ≠ 6 := by
    intro h6
    have hidx2 : H.index = 2 := by
      have := H.index_mul_card; rw [hG, h6] at this; omega
    haveI hn : H.Normal := Subgroup.normal_of_index_eq_two hidx2
    have hsub : {g : G | orderOf g = 3} ⊆ (H : Set G) := by
      intro g hg
      have hg3 : g ^ 3 = 1 := by rw [← hg]; exact pow_orderOf_eq_one g
      have hq2 : Nat.card (G ⧸ H) = 2 := by rw [← Subgroup.index_eq_card, hidx2]
      have h2 : ((g : G ⧸ H)) ^ 2 = 1 := by
        have := pow_card_eq_one' (G := G ⧸ H) (x := (g : G ⧸ H))
        rwa [hq2] at this
      have h3 : ((g : G ⧸ H)) ^ 3 = 1 := by rw [← QuotientGroup.mk_pow, hg3, QuotientGroup.mk_one]
      have h1 : (g : G ⧸ H) = 1 := by
        have e : (g : G ⧸ H) = (g : G ⧸ H) ^ 3 * ((g : G ⧸ H) ^ 2)⁻¹ := by
          simp only [pow_succ, pow_zero, one_mul]; group
        rw [e, h3, h2]; group
      exact (QuotientGroup.eq_one_iff g).mp h1
    have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [ncard_orderOf_eq_three hG hexp, ← Nat.card_coe_set_eq] at hle
    change 8 ≤ Nat.card H at hle
    omega
  have hHcases : Nat.card H = 1 ∨ Nat.card H = 2 ∨ Nat.card H = 3 ∨ Nat.card H = 4 ∨
      Nat.card H = 12 := by
    have hle := Nat.le_of_dvd (by norm_num) hHdvd
    interval_cases h : (Nat.card H) <;> first | omega | (norm_num at hHdvd)

  have fix_zero : ∀ g : G, (∀ x : G, x⁻¹ * g * x ∉ H) → Nat.card (fixedBy X g) = 0 := by
    intro g hg
    have h0 : Nat.card {x : G // x⁻¹ * g * x ∈ H} = 0 := by
      rw [Nat.card_eq_zero]; left; exact ⟨fun x => hg x.1 x.2⟩
    have := key g
    rw [h0] at this
    exact (mul_eq_zero.mp this).resolve_right hHpos.ne'
  have fix_of_count : ∀ (g : G) (m : ℕ), Nat.card {x : G // x⁻¹ * g * x ∈ H} = m * Nat.card H →
      Nat.card (fixedBy X g) = m := by
    intro g m hn
    have := key g
    rw [hn] at this
    exact Nat.eq_of_mul_eq_mul_right hHpos this

  have fix_one : ∀ g : G, Nat.card X = 1 → Nat.card (fixedBy X g) = 1 := by
    intro g h1
    haveI : Subsingleton X := (Nat.card_eq_one_iff_unique.mp h1).1
    have : fixedBy X g = Set.univ := Set.eq_univ_of_forall fun x => Subsingleton.elim _ _
    rw [this, Nat.card_coe_set_eq, Set.ncard_univ, h1]

  have ord_dvd : ∀ {y : G}, y ∈ H → orderOf y ∣ Nat.card H := fun hy => Subgroup.orderOf_dvd_natCard H hy

  have exists_ne_one : 1 < Nat.card H → ∃ y : G, y ∈ H ∧ y ≠ 1 := by
    intro hlt
    haveI := (Finite.one_lt_card_iff_nontrivial.mp hlt)
    obtain ⟨⟨y, hy⟩, hy1⟩ := exists_ne (1 : H)
    exact ⟨y, hy, fun h => hy1 (Subtype.ext h)⟩

  have ncard_image : ∀ (S : Set G) (x : G), ((fun y => y * x) '' S).ncard = S.ncard := fun S x =>
    Set.ncard_image_of_injective S (mul_left_injective x)
  refine ⟨by rcases hHcases with h | h | h | h | h <;> · rw [h] at hHX; omega, ?_, ?_⟩
  ·
    intro a ha1 ha2
    have hoa : orderOf a = 2 := orderOf_eq_two_of_sq ha2 ha1
    have haa : a * a = 1 := by rw [← sq]; exact ha2
    have hcsq : ∀ x : G, (x⁻¹ * a * x) ^ 2 = 1 := fun x => by
      calc (x⁻¹ * a * x) ^ 2 = x⁻¹ * (a * a) * x := by simp only [sq]; group
        _ = 1 := by rw [haa]; group
    have hcne : ∀ x : G, x⁻¹ * a * x ≠ 1 := fun x h => ha1 (by
      calc a = x * (x⁻¹ * a * x) * x⁻¹ := by group
        _ = 1 := by rw [h]; group)
    have hoc : ∀ x : G, orderOf (x⁻¹ * a * x) = 2 := fun x => orderOf_eq_two_of_sq (hcsq x) (hcne x)

    have result : ∃ n v : ℕ, Nat.card X = n ∧ Nat.card (fixedBy X a) = v ∧
        ((n = 1 ∧ v = 1) ∨ (n = 3 ∧ v = 3) ∨ (n = 4 ∧ v = 0) ∨ (n = 6 ∧ v = 2) ∨ (n = 12 ∧ v = 0)) := by
      rcases hHcases with h | h | h | h | h
      ·
        refine ⟨12, 0, by rw [h] at hHX; omega, fix_zero a fun x hx => ?_, by simp⟩
        rw [Subgroup.eq_bot_of_card_eq H h, Subgroup.mem_bot] at hx
        exact hcne x hx
      ·
        obtain ⟨τ, hτH, hτ1⟩ := exists_ne_one (by omega)
        have hτ2 : τ ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp (h ▸ ord_dvd hτH)
        have hoτ : orderOf τ = 2 := orderOf_eq_two_of_sq hτ2 hτ1
        have hHset : (H : Set G) = {1, τ} := by
          symm
          apply Set.eq_of_subset_of_ncard_le
          · intro y hy
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
            rcases hy with rfl | rfl
            · exact H.one_mem
            · exact hτH
          · rw [Set.ncard_pair (Ne.symm hτ1), ← Nat.card_coe_set_eq]
            exact h.le
          · exact Set.toFinite _
        have hmemH : ∀ y : G, y ∈ H ↔ y = 1 ∨ y = τ := by
          intro y
          rw [← SetLike.mem_coe, hHset]
          simp
        obtain ⟨x₀, hx₀⟩ := exists_conj_eq hG hexp hoa hoτ
        have hset : {x : G | x⁻¹ * a * x ∈ H} = (fun y => y * x₀) '' {y : G | y ^ 2 = 1} := by
          ext x
          simp only [Set.mem_setOf_eq, Set.mem_image]
          constructor
          · intro hx
            rw [hmemH] at hx
            rcases hx with hx | hx
            · exact absurd hx (hcne x)
            · refine ⟨x * x₀⁻¹, ?_, by group⟩
              rw [← mul_eq_mul_iff_sq_eq_one hG hexp hoa]

              have e : x⁻¹ * a * x = x₀⁻¹ * a * x₀ := by rw [hx, hx₀]
              calc x * x₀⁻¹ * a = x * (x₀⁻¹ * a * x₀) * x₀⁻¹ := by group
                _ = x * (x⁻¹ * a * x) * x₀⁻¹ := by rw [e]
                _ = a * (x * x₀⁻¹) := by group
          · rintro ⟨y, hy, rfl⟩
            rw [← mul_eq_mul_iff_sq_eq_one hG hexp hoa] at hy
            rw [hmemH]; right
            calc (y * x₀)⁻¹ * a * (y * x₀) = x₀⁻¹ * (y⁻¹ * (a * y)) * x₀ := by group
              _ = x₀⁻¹ * (y⁻¹ * (y * a)) * x₀ := by rw [hy]
              _ = x₀⁻¹ * a * x₀ := by group
              _ = τ := hx₀
        refine ⟨6, 2, by rw [h] at hHX; omega, fix_of_count a 2 ?_, by simp⟩
        change Nat.card ({x : G | x⁻¹ * a * x ∈ H} : Set G) = 2 * Nat.card H
        rw [h, Nat.card_coe_set_eq, hset, ncard_image, ncard_sq_eq_one hG hexp]
      ·
        refine ⟨4, 0, by rw [h] at hHX; omega, fix_zero a fun x hx => ?_, by simp⟩
        have := ord_dvd hx
        rw [hoc x, h] at this
        norm_num at this
      ·
        refine ⟨3, 3, by rw [h] at hHX; omega, fix_of_count a 3 ?_, by simp⟩
        have : ∀ x : G, x⁻¹ * a * x ∈ H := fun x =>
          (mem_iff_sq_eq_one_of_card_eq_four hG hexp h _).mpr (hcsq x)
        rw [h, Nat.card_congr (Equiv.subtypeUnivEquiv this), hG]
      ·
        refine ⟨1, 1, by rw [h] at hHX; omega, fix_one a (by rw [h] at hHX; omega), by simp⟩
    obtain ⟨n, v, hn, hv, hcases⟩ := result
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩ <;>
      rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega
  ·
    intro b hb1 hb3
    have hob : orderOf b = 3 := orderOf_eq_three_of_cube hb3 hb1
    have hcpow : ∀ x : G, (x⁻¹ * b * x) ^ 3 = 1 := fun x => by
      calc (x⁻¹ * b * x) ^ 3 = x⁻¹ * b ^ 3 * x := by
            simp only [pow_succ, pow_zero, one_mul]; group
        _ = 1 := by rw [hb3]; group
    have hcne : ∀ x : G, x⁻¹ * b * x ≠ 1 := fun x h => hb1 (by
      calc b = x * (x⁻¹ * b * x) * x⁻¹ := by group
        _ = 1 := by rw [h]; group)
    have hoc : ∀ x : G, orderOf (x⁻¹ * b * x) = 3 := fun x => orderOf_eq_three_of_cube (hcpow x) (hcne x)
    have hcsq : ∀ x : G, (x⁻¹ * b * x) ^ 2 ≠ 1 := fun x h2 => by
      have := orderOf_dvd_of_pow_eq_one h2
      rw [hoc x] at this; norm_num at this
    have result : ∃ n v : ℕ, Nat.card X = n ∧ Nat.card (fixedBy X b) = v ∧
        ((n = 1 ∧ v = 1) ∨ (n = 3 ∧ v = 0) ∨ (n = 4 ∧ v = 1) ∨ (n = 6 ∧ v = 0) ∨ (n = 12 ∧ v = 0)) := by
      rcases hHcases with h | h | h | h | h
      · refine ⟨12, 0, by rw [h] at hHX; omega, fix_zero b fun x hx => ?_, by simp⟩
        rw [Subgroup.eq_bot_of_card_eq H h, Subgroup.mem_bot] at hx
        exact hcne x hx
      ·
        refine ⟨6, 0, by rw [h] at hHX; omega, fix_zero b fun x hx => ?_, by simp⟩
        have := ord_dvd hx
        rw [hoc x, h] at this
        norm_num at this
      ·
        obtain ⟨c, hcH, hc1⟩ := exists_ne_one (by omega)
        have hocc : orderOf c = 3 := orderOf_eq_three_of_mem h hcH hc1
        have hc3 : c ^ 3 = 1 := by rw [← hocc]; exact pow_orderOf_eq_one c

        obtain ⟨x₀, hx₀⟩ : ∃ x₀ : G, x₀⁻¹ * b * x₀ ∈ H := by
          let PH : Sylow 3 G := Sylow.ofCard H (by rw [hG, factorization_twelve_three, pow_one]; exact h)
          obtain ⟨Pb, hbPb⟩ := exists_sylow_mem_of_orderOf hob
          obtain ⟨g, hg⟩ := exists_smul_eq G Pb PH
          refine ⟨g⁻¹, ?_⟩
          have : g * b * g⁻¹ ∈ ((g • Pb : Sylow 3 G) : Subgroup G) := by
            rw [mem_smul_sylow_iff]
            have e : g⁻¹ * (g * b * g⁻¹) * g = b := by group
            rw [e]; exact hbPb
          rw [hg] at this
          simpa [PH, Sylow.coe_ofCard] using this
        have hset : {x : G | x⁻¹ * b * x ∈ H} = (fun y => y * x₀) '' (Subgroup.zpowers b : Set G) := by
          ext x
          simp only [Set.mem_setOf_eq, Set.mem_image, SetLike.mem_coe]
          constructor
          · intro hx

            have hd := mem_of_card_three h hcH hc1 hx
            have hd₀ := mem_of_card_three h hcH hc1 hx₀
            refine ⟨x * x₀⁻¹, ?_, by group⟩

            suffices heq : x⁻¹ * b * x = x₀⁻¹ * b * x₀ by
              apply mem_zpowers_of_mul_eq_mul hG hexp hob
              calc x * x₀⁻¹ * b = x * (x₀⁻¹ * b * x₀) * x₀⁻¹ := by group
                _ = x * (x⁻¹ * b * x) * x₀⁻¹ := by rw [heq]
                _ = b * (x * x₀⁻¹) := by group

            have hz : (x₀⁻¹ * x)⁻¹ * (x₀⁻¹ * b * x₀) * (x₀⁻¹ * x) = x⁻¹ * b * x := by group
            rcases hd with hd | hd | hd
            · exact absurd hd (hcne x)
            rcases hd₀ with hd₀ | hd₀ | hd₀
            · exact absurd hd₀ (hcne x₀)
            · rw [hd, hd₀]
            · exfalso
              rw [hd, hd₀] at hz

              have hocc2 : orderOf (c ^ 2) = 3 := by
                apply orderOf_eq_three_of_cube
                · rw [← pow_mul, show 2 * 3 = 3 * 2 by norm_num, pow_mul, hc3, one_pow]
                · intro h2
                  apply hc1
                  calc c = c ^ 3 * (c ^ 2)⁻¹ := by simp only [pow_succ, pow_zero, one_mul]; group
                    _ = 1 := by rw [hc3, h2]; group
              apply conj_ne_sq hG hexp hocc2 (z := x₀⁻¹ * x)
              rw [hz]
              calc c = c ^ 3 * c := by rw [hc3, one_mul]
                _ = (c ^ 2) ^ 2 := by simp only [pow_succ, pow_zero, one_mul]; group
            rcases hd₀ with hd₀ | hd₀ | hd₀
            · exact absurd hd₀ (hcne x₀)
            · exfalso
              rw [hd, hd₀] at hz
              exact conj_ne_sq hG hexp hocc hz
            · rw [hd, hd₀]
          · rintro ⟨y, hy, rfl⟩
            rw [Subgroup.mem_zpowers_iff] at hy
            obtain ⟨k, rfl⟩ := hy
            have hc : Commute (b ^ k) b := (Commute.refl b).zpow_left k
            have hcomm : (b ^ k)⁻¹ * b * b ^ k = b := by
              rw [mul_assoc, ← hc.eq, ← mul_assoc, inv_mul_cancel, one_mul]
            have e : (b ^ k * x₀)⁻¹ * b * (b ^ k * x₀) = x₀⁻¹ * b * x₀ := by
              calc (b ^ k * x₀)⁻¹ * b * (b ^ k * x₀) = x₀⁻¹ * ((b ^ k)⁻¹ * b * b ^ k) * x₀ := by group
                _ = x₀⁻¹ * b * x₀ := by rw [hcomm]
            rw [e]
            exact hx₀
        refine ⟨4, 1, by rw [h] at hHX; omega, fix_of_count b 1 ?_, by simp⟩
        change Nat.card ({x : G | x⁻¹ * b * x ∈ H} : Set G) = 1 * Nat.card H
        rw [h, Nat.card_coe_set_eq, hset, ncard_image, ← Nat.card_coe_set_eq]
        change Nat.card (Subgroup.zpowers b) = 1 * 3
        rw [Nat.card_zpowers, hob]
      ·
        refine ⟨3, 0, by rw [h] at hHX; omega, fix_zero b fun x hx => ?_, by simp⟩
        exact hcsq x ((mem_iff_sq_eq_one_of_card_eq_four hG hexp h _).mp hx)
      · refine ⟨1, 1, by rw [h] at hHX; omega, fix_one b (by rw [h] at hHX; omega), by simp⟩
    obtain ⟨n, v, hn, hv, hcases⟩ := result
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩ <;>
      rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega

end Marks

end P2MKcMarksA4
p2m_reactivate "P2MW.S_MulAction_natCard_fixedBy_of_isPretransitive_of_card_eq_twelve.P2MKcMarksA4"

theorem solution
    {G : Type*} [Group G] [Finite G] (hG : Nat.card G = 12)
    (hG' : ∀ g : G, g ^ 2 = 1 ∨ g ^ 3 = 1)
    (X : Type*) [MulAction G X] [Nonempty X] [MulAction.IsPretransitive G X] :
    (Nat.card X = 1 ∨ Nat.card X = 3 ∨ Nat.card X = 4 ∨ Nat.card X = 6 ∨ Nat.card X = 12) ∧
    (∀ a : G, a ≠ 1 → a ^ 2 = 1 →
      (Nat.card X = 1 → Nat.card (MulAction.fixedBy X a) = 1) ∧
      (Nat.card X = 3 → Nat.card (MulAction.fixedBy X a) = 3) ∧
      (Nat.card X = 4 → Nat.card (MulAction.fixedBy X a) = 0) ∧
      (Nat.card X = 6 → Nat.card (MulAction.fixedBy X a) = 2) ∧
      (Nat.card X = 12 → Nat.card (MulAction.fixedBy X a) = 0)) ∧
    (∀ b : G, b ≠ 1 → b ^ 3 = 1 →
      (Nat.card X = 1 → Nat.card (MulAction.fixedBy X b) = 1) ∧
      (Nat.card X = 3 → Nat.card (MulAction.fixedBy X b) = 0) ∧
      (Nat.card X = 4 → Nat.card (MulAction.fixedBy X b) = 1) ∧
      (Nat.card X = 6 → Nat.card (MulAction.fixedBy X b) = 0) ∧
      (Nat.card X = 12 → Nat.card (MulAction.fixedBy X b) = 0)) :=
  P2MKcMarksA4.marks X hG hG'

end S_MulAction_natCard_fixedBy_of_isPretransitive_of_card_eq_twelve
end P2MW
export P2MW.S_MulAction_natCard_fixedBy_of_isPretransitive_of_card_eq_twelve (solution)
