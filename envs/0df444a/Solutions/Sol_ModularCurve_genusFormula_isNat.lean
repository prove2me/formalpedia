-- Prove2me | solution 1 for ModularCurve.genusFormula_isNat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/56fadd9a-5f57-5437-8934-38bdb09b1eef

import Mathlib
import Definitions.Def_ModularCurve_GenusNumerics
import Theorems.Thm_ModularCurve_cuspCount_prime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_genusFormula_isNat

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace ModularCurve
p2m_export "ModularCurve" "nuTwo nuThree cuspCount cuspCount_one genusFormula dedekindPsi dedekindPsi_one ModularPolynomialData ModularPolynomialData.natDegree_eq cuspCount_prime"
p2m_open "ModularCurve"

theorem dedekindPsi_prime {p : ℕ} (hp : p.Prime) : dedekindPsi p = p + 1 := by
  rw [dedekindPsi, hp.divisors]
  rw [Finset.filter_true_of_mem]
  · rw [Finset.sum_pair hp.one_lt.ne]
    rw [Nat.div_one, Nat.div_self hp.pos]
  · rintro d hd
    rcases Finset.mem_insert.mp hd with rfl | hd
    · exact squarefree_one
    · rw [Finset.mem_singleton] at hd
      subst hd
      exact hp.squarefree

theorem dedekindPsi_two : dedekindPsi 2 = 3 := by
  rw [dedekindPsi_prime Nat.prime_two]

end ModularCurve

namespace ModularCurve
p2m_export "ModularCurve" "nuTwo nuThree cuspCount cuspCount_one genusFormula dedekindPsi dedekindPsi_one ModularPolynomialData ModularPolynomialData.natDegree_eq cuspCount_prime"
p2m_open "ModularCurve"

theorem not_sq_add_one_eq_zero_zmod_four (y : ZMod 4) : y ^ 2 + 1 ≠ 0 := by
  revert y
  decide

theorem nuTwo_eq_zero_of_four_dvd {N : ℕ} (h : 4 ∣ N) : nuTwo N = 0 := by
  have hempty : IsEmpty {x : ZMod N // x ^ 2 + 1 = 0} := by
    refine ⟨fun z => ?_⟩
    obtain ⟨x, hx⟩ := z
    refine not_sq_add_one_eq_zero_zmod_four (ZMod.castHom h (ZMod 4) x) ?_
    have hx4 := congrArg (ZMod.castHom h (ZMod 4)) hx
    simpa only [map_add, map_pow, map_one, map_zero] using hx4
  exact @Nat.card_of_isEmpty _ hempty

section Prime

variable {p : ℕ}

theorem sq_add_one_eq_zero_iff_of_prime (hp : p.Prime) {s x : ZMod p}
    (hs : s ^ 2 + 1 = 0) : x ^ 2 + 1 = 0 ↔ x = s ∨ x = -s := by
  haveI : Fact p.Prime := ⟨hp⟩
  constructor
  · intro hx
    have hfac : (x - s) * (x + s) = 0 := by linear_combination hx - hs
    rcases mul_eq_zero.mp hfac with hd | hd
    · exact Or.inl (by linear_combination hd)
    · exact Or.inr (by linear_combination hd)
  · rintro (rfl | rfl)
    · exact hs
    · linear_combination hs

theorem ne_zero_of_sq_add_one_eq_zero (hp : p.Prime) {s : ZMod p} (hs : s ^ 2 + 1 = 0) :
    s ≠ 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  rintro rfl
  exact one_ne_zero (α := ZMod p) (by linear_combination hs)

theorem ne_neg_self_of_sq_add_one_eq_zero (hp : p.Prime) (hp2 : p ≠ 2) {s : ZMod p}
    (hs : s ^ 2 + 1 = 0) : s ≠ -s := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro hcontra
  have h2s : (2 : ZMod p) * s = 0 := by linear_combination hcontra
  rcases mul_eq_zero.mp h2s with h2 | hs0
  ·
    have hcast : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h2
    have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp hcast
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hdvd)
  · exact ne_zero_of_sq_add_one_eq_zero hp hs hs0

theorem nuTwo_prime (hp : p.Prime) (hp2 : p ≠ 2) :
    nuTwo p = if p % 4 = 1 then 2 else 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_cases h1 : p % 4 = 1
  ·

    rw [if_pos h1]
    obtain ⟨s, hs⟩ : IsSquare (-1 : ZMod p) :=
      ZMod.exists_sq_eq_neg_one_iff.mpr (by omega)
    have hs2 : s ^ 2 + 1 = 0 := by linear_combination -hs
    have hns2 : (-s) ^ 2 + 1 = 0 := by linear_combination hs2
    have hne : s ≠ -s := ne_neg_self_of_sq_add_one_eq_zero hp hp2 hs2
    show Nat.card {x : ZMod p // x ^ 2 + 1 = 0} = 2
    rw [Nat.card_eq_two_iff]
    refine ⟨⟨s, hs2⟩, ⟨-s, hns2⟩, ?_, ?_⟩
    · simp only [ne_eq, Subtype.mk.injEq]
      exact hne
    · rw [Set.eq_univ_iff_forall]
      rintro ⟨x, hx⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Subtype.mk.injEq]
      exact (sq_add_one_eq_zero_iff_of_prime hp hs2).mp hx
  ·
    rw [if_neg h1]

    have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
    have hns : ¬IsSquare (-1 : ZMod p) := by
      rw [ZMod.exists_sq_eq_neg_one_iff]
      omega
    have hempty : IsEmpty {x : ZMod p // x ^ 2 + 1 = 0} := by
      refine ⟨fun z => ?_⟩
      obtain ⟨x, hx⟩ := z
      exact hns ⟨x, by linear_combination -hx⟩
    exact @Nat.card_of_isEmpty _ hempty

theorem nuTwo_eq_zero_of_mod_four_eq_three (hp : p.Prime) (h3 : p % 4 = 3) :
    nuTwo p = 0 := by
  have hp2 : p ≠ 2 := by
    rintro rfl
    omega
  have hne1 : ¬p % 4 = 1 := by omega
  rw [nuTwo_prime hp hp2, if_neg hne1]

theorem nuTwo_eq_two_of_mod_four_eq_one (hp : p.Prime) (h1 : p % 4 = 1) :
    nuTwo p = 2 := by
  have hp2 : p ≠ 2 := by
    rintro rfl
    omega
  rw [nuTwo_prime hp hp2, if_pos h1]

end Prime

section Multiplicative

variable {A B : Type*} [Ring A] [Ring B]

theorem fst_sq_add_one (y : A × B) : (y ^ 2 + 1).1 = y.1 ^ 2 + 1 := by
  rw [pow_two, pow_two, Prod.fst_add, Prod.fst_mul, Prod.fst_one]

theorem snd_sq_add_one (y : A × B) : (y ^ 2 + 1).2 = y.2 ^ 2 + 1 := by
  rw [pow_two, pow_two, Prod.snd_add, Prod.snd_mul, Prod.snd_one]

theorem sq_add_one_eq_zero_prod_iff (y : A × B) :
    y ^ 2 + 1 = 0 ↔ y.1 ^ 2 + 1 = 0 ∧ y.2 ^ 2 + 1 = 0 := by
  constructor
  · intro hy
    refine ⟨?_, ?_⟩
    · rw [← fst_sq_add_one, hy, Prod.fst_zero]
    · rw [← snd_sq_add_one, hy, Prod.snd_zero]
  · rintro ⟨h1, h2⟩
    calc y ^ 2 + 1 = ((y ^ 2 + 1).1, (y ^ 2 + 1).2) := rfl
      _ = ((0 : A), (0 : B)) := by rw [fst_sq_add_one, snd_sq_add_one, h1, h2]
      _ = (0 : A × B) := rfl

theorem sq_add_one_eq_zero_iff_map {R S : Type*} [Ring R] [Ring S] (f : R ≃+* S) (x : R) :
    x ^ 2 + 1 = 0 ↔ f x ^ 2 + 1 = 0 := by
  constructor
  · intro hx
    have hmap := congrArg f hx
    simpa only [map_add, map_pow, map_one, map_zero] using hmap
  · intro hx
    have hmap := congrArg f.symm hx
    simpa only [map_add, map_pow, map_one, map_zero, RingEquiv.symm_apply_apply] using hmap

end Multiplicative

theorem nuTwo_mul_of_coprime {M N : ℕ} (h : Nat.Coprime M N) :
    nuTwo (M * N) = nuTwo M * nuTwo N := by
  have key : ∀ x : ZMod (M * N),
      x ^ 2 + 1 = 0 ↔
        ((ZMod.chineseRemainder h) x).1 ^ 2 + 1 = 0 ∧
          ((ZMod.chineseRemainder h) x).2 ^ 2 + 1 = 0 := by
    intro x
    rw [sq_add_one_eq_zero_iff_map (ZMod.chineseRemainder h) x,
      sq_add_one_eq_zero_prod_iff]
  have e₁ : {x : ZMod (M * N) // x ^ 2 + 1 = 0} ≃
      {c : ZMod M × ZMod N // c.1 ^ 2 + 1 = 0 ∧ c.2 ^ 2 + 1 = 0} :=
    Equiv.subtypeEquiv (ZMod.chineseRemainder h).toEquiv key
  have e₂ : {c : ZMod M × ZMod N // c.1 ^ 2 + 1 = 0 ∧ c.2 ^ 2 + 1 = 0} ≃
      {a : ZMod M // a ^ 2 + 1 = 0} × {b : ZMod N // b ^ 2 + 1 = 0} :=
    Equiv.subtypeProdEquivProd
      (p := fun a : ZMod M => a ^ 2 + 1 = 0) (q := fun b : ZMod N => b ^ 2 + 1 = 0)
  show Nat.card {x : ZMod (M * N) // x ^ 2 + 1 = 0} =
    Nat.card {a : ZMod M // a ^ 2 + 1 = 0} * Nat.card {b : ZMod N // b ^ 2 + 1 = 0}
  rw [Nat.card_congr (e₁.trans e₂), Nat.card_prod]

theorem nuTwo_one : nuTwo 1 = 1 := by
  have hcard : nuTwo 1 = Fintype.card {x : ZMod 1 // x ^ 2 + 1 = 0} :=
    Nat.card_eq_fintype_card
  rw [hcard]
  decide

theorem nuTwo_two : nuTwo 2 = 1 := by
  have hcard : nuTwo 2 = Fintype.card {x : ZMod 2 // x ^ 2 + 1 = 0} :=
    Nat.card_eq_fintype_card
  rw [hcard]
  decide

theorem nuTwo_five : nuTwo 5 = 2 :=
  nuTwo_eq_two_of_mod_four_eq_one (by norm_num) (by norm_num)

theorem nuTwo_eleven : nuTwo 11 = 0 :=
  nuTwo_eq_zero_of_mod_four_eq_three (by norm_num) (by norm_num)

theorem nuTwo_thirteen : nuTwo 13 = 2 :=
  nuTwo_eq_two_of_mod_four_eq_one (by norm_num) (by norm_num)

end ModularCurve

namespace ModularCurve
p2m_export "ModularCurve" "nuTwo nuThree cuspCount cuspCount_one genusFormula dedekindPsi dedekindPsi_one ModularPolynomialData ModularPolynomialData.natDegree_eq cuspCount_prime"
p2m_open "ModularCurve"

theorem not_sq_add_self_add_one_eq_zero_zmod_nine (y : ZMod 9) : y ^ 2 + y + 1 ≠ 0 := by
  revert y
  decide

theorem nuThree_eq_zero_of_nine_dvd {N : ℕ} (h : 9 ∣ N) : nuThree N = 0 := by
  have hempty : IsEmpty {x : ZMod N // x ^ 2 + x + 1 = 0} := by
    refine ⟨fun z => ?_⟩
    obtain ⟨x, hx⟩ := z
    refine not_sq_add_self_add_one_eq_zero_zmod_nine (ZMod.castHom h (ZMod 9) x) ?_
    have hx9 := congrArg (ZMod.castHom h (ZMod 9)) hx
    simpa only [map_add, map_pow, map_one, map_zero] using hx9
  exact @Nat.card_of_isEmpty _ hempty

section Prime

variable {p : ℕ}

theorem sq_add_self_add_one_eq_zero_iff_orderOf_eq_three (hp : p.Prime) (hp3 : p ≠ 3)
    (x : ZMod p) : x ^ 2 + x + 1 = 0 ↔ orderOf x = 3 := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  constructor
  · intro hx
    refine orderOf_eq_prime ?_ ?_
    ·
      linear_combination (x - 1) * hx
    ·
      rintro rfl
      have h3 : (3 : ZMod p) = 0 := by linear_combination hx
      have hcast : ((3 : ℕ) : ZMod p) = 0 := by exact_mod_cast h3
      have hdvd : p ∣ 3 := (CharP.cast_eq_zero_iff (ZMod p) p 3).mp hcast
      exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hdvd)
  · intro hx
    have hx3 : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
    have hx1 : x ≠ 1 := by
      rintro rfl
      rw [orderOf_one] at hx
      omega
    have hfac : (x - 1) * (x ^ 2 + x + 1) = 0 := by linear_combination hx3
    rcases mul_eq_zero.mp hfac with h | h
    · exact absurd (by linear_combination h : x = 1) hx1
    · exact h

theorem sq_add_self_add_one_eq_zero_iff_of_prime (hp : p.Prime) {ζ x : ZMod p}
    (hζ : ζ ^ 2 + ζ + 1 = 0) : x ^ 2 + x + 1 = 0 ↔ x = ζ ∨ x = -1 - ζ := by
  haveI : Fact p.Prime := ⟨hp⟩
  constructor
  · intro hx
    have hfac : (x - ζ) * (x + ζ + 1) = 0 := by linear_combination hx - hζ
    rcases mul_eq_zero.mp hfac with hd | hd
    · exact Or.inl (by linear_combination hd)
    · exact Or.inr (by linear_combination hd)
  · rintro (rfl | rfl)
    · exact hζ
    · linear_combination hζ

theorem ne_neg_one_sub_of_sq_add_self_add_one_eq_zero (hp : p.Prime) (hp3 : p ≠ 3)
    {ζ : ZMod p} (hζ : ζ ^ 2 + ζ + 1 = 0) : ζ ≠ -1 - ζ := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro hcontra
  have h3 : (3 : ZMod p) = 0 := by linear_combination 4 * hζ - (2 * ζ + 1) * hcontra
  have hcast : ((3 : ℕ) : ZMod p) = 0 := by exact_mod_cast h3
  have hdvd : p ∣ 3 := (CharP.cast_eq_zero_iff (ZMod p) p 3).mp hcast
  exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hdvd)

theorem exists_orderOf_eq_three (hp : p.Prime) (h1 : p % 3 = 1) :
    ∃ x : ZMod p, orderOf x = 3 := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hdvd : 3 ∣ Fintype.card (ZMod p)ˣ := by
    rw [ZMod.card_units p]
    have := hp.two_le
    omega
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card 3 hdvd
  exact ⟨(u : ZMod p), by rw [orderOf_units]; exact hu⟩

theorem nuThree_prime (hp : p.Prime) (hp3 : p ≠ 3) :
    nuThree p = if p % 3 = 1 then 2 else 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_cases h1 : p % 3 = 1
  ·

    rw [if_pos h1]
    obtain ⟨ζ, hζord⟩ := exists_orderOf_eq_three hp h1
    have hζ : ζ ^ 2 + ζ + 1 = 0 :=
      (sq_add_self_add_one_eq_zero_iff_orderOf_eq_three hp hp3 ζ).mpr hζord
    have hζ' : (-1 - ζ) ^ 2 + (-1 - ζ) + 1 = 0 := by linear_combination hζ
    have hne : ζ ≠ -1 - ζ := ne_neg_one_sub_of_sq_add_self_add_one_eq_zero hp hp3 hζ
    show Nat.card {x : ZMod p // x ^ 2 + x + 1 = 0} = 2
    rw [Nat.card_eq_two_iff]
    refine ⟨⟨ζ, hζ⟩, ⟨-1 - ζ, hζ'⟩, ?_, ?_⟩
    · simp only [ne_eq, Subtype.mk.injEq]
      exact hne
    · rw [Set.eq_univ_iff_forall]
      rintro ⟨x, hx⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Subtype.mk.injEq]
      exact (sq_add_self_add_one_eq_zero_iff_of_prime hp hζ).mp hx
  ·

    rw [if_neg h1]
    have hempty : IsEmpty {x : ZMod p // x ^ 2 + x + 1 = 0} := by
      refine ⟨fun z => ?_⟩
      obtain ⟨x, hx⟩ := z
      have hord : orderOf x = 3 :=
        (sq_add_self_add_one_eq_zero_iff_orderOf_eq_three hp hp3 x).mp hx
      have hx0 : x ≠ 0 := by
        rintro rfl
        exact one_ne_zero (α := ZMod p) (by linear_combination hx)
      have hdvd : (3 : ℕ) ∣ p - 1 := by
        rw [← hord]
        exact ZMod.orderOf_dvd_card_sub_one hx0
      have := hp.two_le
      omega
    exact @Nat.card_of_isEmpty _ hempty

theorem nuThree_eq_zero_of_mod_three_eq_two (hp : p.Prime) (h2 : p % 3 = 2) :
    nuThree p = 0 := by
  have hp3 : p ≠ 3 := by rintro rfl; omega
  have hne1 : ¬p % 3 = 1 := by omega
  rw [nuThree_prime hp hp3, if_neg hne1]

theorem nuThree_eq_two_of_mod_three_eq_one (hp : p.Prime) (h1 : p % 3 = 1) :
    nuThree p = 2 := by
  have hp3 : p ≠ 3 := by rintro rfl; omega
  rw [nuThree_prime hp hp3, if_pos h1]

end Prime

theorem nuThree_three : nuThree 3 = 1 := by
  have hcard : nuThree 3 = Fintype.card {x : ZMod 3 // x ^ 2 + x + 1 = 0} :=
    Nat.card_eq_fintype_card
  rw [hcard]
  decide

section Multiplicative

variable {A B : Type*} [Ring A] [Ring B]

theorem fst_sq_add_self_add_one (y : A × B) : (y ^ 2 + y + 1).1 = y.1 ^ 2 + y.1 + 1 := by
  rw [pow_two, pow_two, Prod.fst_add, Prod.fst_add, Prod.fst_mul, Prod.fst_one]

theorem snd_sq_add_self_add_one (y : A × B) : (y ^ 2 + y + 1).2 = y.2 ^ 2 + y.2 + 1 := by
  rw [pow_two, pow_two, Prod.snd_add, Prod.snd_add, Prod.snd_mul, Prod.snd_one]

theorem sq_add_self_add_one_eq_zero_prod_iff (y : A × B) :
    y ^ 2 + y + 1 = 0 ↔ y.1 ^ 2 + y.1 + 1 = 0 ∧ y.2 ^ 2 + y.2 + 1 = 0 := by
  constructor
  · intro hy
    refine ⟨?_, ?_⟩
    · rw [← fst_sq_add_self_add_one, hy, Prod.fst_zero]
    · rw [← snd_sq_add_self_add_one, hy, Prod.snd_zero]
  · rintro ⟨h1, h2⟩
    calc y ^ 2 + y + 1 = ((y ^ 2 + y + 1).1, (y ^ 2 + y + 1).2) := rfl
      _ = ((0 : A), (0 : B)) := by
          rw [fst_sq_add_self_add_one, snd_sq_add_self_add_one, h1, h2]
      _ = (0 : A × B) := rfl

theorem sq_add_self_add_one_eq_zero_iff_map {R S : Type*} [Ring R] [Ring S] (f : R ≃+* S)
    (x : R) : x ^ 2 + x + 1 = 0 ↔ f x ^ 2 + f x + 1 = 0 := by
  constructor
  · intro hx
    have hmap := congrArg f hx
    simpa only [map_add, map_pow, map_one, map_zero] using hmap
  · intro hx
    have hmap := congrArg f.symm hx
    simpa only [map_add, map_pow, map_one, map_zero, RingEquiv.symm_apply_apply] using hmap

end Multiplicative

theorem nuThree_mul_of_coprime {M N : ℕ} (h : Nat.Coprime M N) :
    nuThree (M * N) = nuThree M * nuThree N := by
  have key : ∀ x : ZMod (M * N),
      x ^ 2 + x + 1 = 0 ↔
        ((ZMod.chineseRemainder h) x).1 ^ 2 + ((ZMod.chineseRemainder h) x).1 + 1 = 0 ∧
          ((ZMod.chineseRemainder h) x).2 ^ 2 + ((ZMod.chineseRemainder h) x).2 + 1 = 0 := by
    intro x
    rw [sq_add_self_add_one_eq_zero_iff_map (ZMod.chineseRemainder h) x,
      sq_add_self_add_one_eq_zero_prod_iff]
  have e₁ : {x : ZMod (M * N) // x ^ 2 + x + 1 = 0} ≃
      {c : ZMod M × ZMod N // c.1 ^ 2 + c.1 + 1 = 0 ∧ c.2 ^ 2 + c.2 + 1 = 0} :=
    Equiv.subtypeEquiv (ZMod.chineseRemainder h).toEquiv key
  have e₂ : {c : ZMod M × ZMod N // c.1 ^ 2 + c.1 + 1 = 0 ∧ c.2 ^ 2 + c.2 + 1 = 0} ≃
      {a : ZMod M // a ^ 2 + a + 1 = 0} × {b : ZMod N // b ^ 2 + b + 1 = 0} :=
    Equiv.subtypeProdEquivProd
      (p := fun a : ZMod M => a ^ 2 + a + 1 = 0)
      (q := fun b : ZMod N => b ^ 2 + b + 1 = 0)
  show Nat.card {x : ZMod (M * N) // x ^ 2 + x + 1 = 0} =
    Nat.card {a : ZMod M // a ^ 2 + a + 1 = 0} * Nat.card {b : ZMod N // b ^ 2 + b + 1 = 0}
  rw [Nat.card_congr (e₁.trans e₂), Nat.card_prod]

theorem nuThree_one : nuThree 1 = 1 := by
  have hcard : nuThree 1 = Fintype.card {x : ZMod 1 // x ^ 2 + x + 1 = 0} :=
    Nat.card_eq_fintype_card
  rw [hcard]
  decide

theorem nuThree_seven : nuThree 7 = 2 :=
  nuThree_eq_two_of_mod_three_eq_one (by norm_num) (by norm_num)

theorem nuThree_eleven : nuThree 11 = 0 :=
  nuThree_eq_zero_of_mod_three_eq_two (by norm_num) (by norm_num)

theorem nuThree_thirteen : nuThree 13 = 2 :=
  nuThree_eq_two_of_mod_three_eq_one (by norm_num) (by norm_num)

theorem nuThree_nineteen : nuThree 19 = 2 :=
  nuThree_eq_two_of_mod_three_eq_one (by norm_num) (by norm_num)

end ModularCurve

namespace ModularCurve
p2m_export "ModularCurve" "nuTwo nuThree cuspCount cuspCount_one genusFormula dedekindPsi dedekindPsi_one ModularPolynomialData ModularPolynomialData.natDegree_eq cuspCount_prime"
p2m_open "ModularCurve"

p2m_open "Finset Nat Finset.Nat ArithmeticFunction"

def squarefreeIndicator : ArithmeticFunction ℕ :=
  ⟨fun n => if Squarefree n then 1 else 0, by simp [not_squarefree_zero]⟩

@[scoped simp]
theorem squarefreeIndicator_apply {n : ℕ} :
    squarefreeIndicator n = if Squarefree n then 1 else 0 :=
  rfl

theorem isMultiplicative_squarefreeIndicator : squarefreeIndicator.IsMultiplicative := by
  refine ⟨by simp, fun {m n} h => ?_⟩
  simp only [squarefreeIndicator_apply, Nat.squarefree_mul h]
  by_cases hm : Squarefree m <;> by_cases hn : Squarefree n <;> simp [hm, hn]

theorem dedekindPsi_eq_mul_apply (N : ℕ) :
    dedekindPsi N = (squarefreeIndicator * ArithmeticFunction.id) N :=
  calc dedekindPsi N
      = ∑ d ∈ N.divisors, squarefreeIndicator d * ArithmeticFunction.id (N / d) := by
        rw [dedekindPsi, sum_filter]
        refine Finset.sum_congr rfl fun d _ => ?_
        by_cases hd : Squarefree d <;> simp [hd]
    _ = ∑ x ∈ N.divisorsAntidiagonal, squarefreeIndicator x.1 * ArithmeticFunction.id x.2 :=
        (Nat.sum_divisorsAntidiagonal fun d e =>
          squarefreeIndicator d * ArithmeticFunction.id e).symm
    _ = (squarefreeIndicator * ArithmeticFunction.id) N := ArithmeticFunction.mul_apply.symm

theorem isMultiplicative_squarefreeIndicator_mul_id :
    (squarefreeIndicator * ArithmeticFunction.id).IsMultiplicative :=
  isMultiplicative_squarefreeIndicator.mul isMultiplicative_id

theorem dedekindPsi_mul_of_coprime (M N : ℕ) (h : Nat.Coprime M N) :
    dedekindPsi (M * N) = dedekindPsi M * dedekindPsi N := by
  simp only [dedekindPsi_eq_mul_apply]
  exact isMultiplicative_squarefreeIndicator_mul_id.map_mul_of_coprime h

theorem squarefree_prime_pow_iff {p : ℕ} (hp : p.Prime) (j : ℕ) :
    Squarefree (p ^ j) ↔ j ≤ 1 := by
  constructor
  · intro hsq
    by_contra hj
    exact hp.one_lt.ne'
      (Nat.isUnit_iff.mp (hsq p (by rw [← pow_two]; exact pow_dvd_pow p (by omega))))
  · intro hj
    interval_cases j
    · simp
    · simpa using hp.prime.squarefree

theorem filter_squarefree_divisors_prime_pow {p : ℕ} (hp : p.Prime) {k : ℕ} (hk : k ≠ 0) :
    {d ∈ (p ^ k).divisors | Squarefree d} = {1, p} := by
  ext d
  simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨hdvd, -⟩, hsq⟩
    obtain ⟨j, hj, rfl⟩ := (Nat.dvd_prime_pow hp).mp hdvd
    have : j ≤ 1 := (squarefree_prime_pow_iff hp j).mp hsq
    interval_cases j
    · exact Or.inl (pow_zero p)
    · exact Or.inr (pow_one p)
  · rintro (rfl | rfl)
    · exact ⟨⟨one_dvd _, pow_ne_zero _ hp.pos.ne'⟩, squarefree_one⟩
    · exact ⟨⟨dvd_pow_self _ hk, pow_ne_zero _ hp.pos.ne'⟩, hp.prime.squarefree⟩

theorem dedekindPsi_prime_pow (p k : ℕ) (hp : p.Prime) (hk : k ≠ 0) :
    dedekindPsi (p ^ k) = p ^ k + p ^ (k - 1) := by
  have hdiv : p ^ k / p = p ^ (k - 1) := by
    conv_lhs => rw [show k = (k - 1) + 1 by omega, pow_succ]
    exact Nat.mul_div_cancel _ hp.pos
  rw [dedekindPsi, filter_squarefree_divisors_prime_pow hp hk,
    Finset.sum_pair hp.one_lt.ne, Nat.div_one, hdiv]

theorem le_dedekindPsi (N : ℕ) (hN : N ≠ 0) : N ≤ dedekindPsi N := by
  rw [dedekindPsi]
  have h1 : (1 : ℕ) ∈ {d ∈ N.divisors | Squarefree d} :=
    Finset.mem_filter.mpr ⟨Nat.one_mem_divisors.mpr hN, squarefree_one⟩
  simpa using Finset.single_le_sum (f := fun d => N / d) (fun d _ => Nat.zero_le _) h1

theorem dedekindPsi_pos (N : ℕ) (hN : N ≠ 0) : 0 < dedekindPsi N :=
  lt_of_lt_of_le (Nat.pos_of_ne_zero hN) (le_dedekindPsi N hN)

end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_genusFormula_isNat.ModularCurve"

open Finset

namespace ModularCurve
p2m_export "ModularCurve" "nuTwo nuThree cuspCount cuspCount_one genusFormula dedekindPsi dedekindPsi_one ModularPolynomialData ModularPolynomialData.natDegree_eq cuspCount_prime"
p2m_open "ModularCurve"

theorem cuspCount_two : cuspCount 2 = 2 := by decide
theorem cuspCount_three : cuspCount 3 = 2 := by decide
theorem cuspCount_four : cuspCount 4 = 3 := by decide

theorem cuspCount_nine : cuspCount 9 = 4 := by decide
theorem cuspCount_eleven : cuspCount 11 = 2 := by decide
theorem cuspCount_fourteen : cuspCount 14 = 4 := by decide
theorem cuspCount_fifteen : cuspCount 15 = 4 := by decide
theorem cuspCount_seventeen : cuspCount 17 = 2 := by decide
theorem cuspCount_nineteen : cuspCount 19 = 2 := by decide
theorem cuspCount_twenty : cuspCount 20 = 6 := by decide
theorem cuspCount_twentyOne : cuspCount 21 = 4 := by decide
theorem cuspCount_twentyFour : cuspCount 24 = 8 := by decide
theorem cuspCount_twentySeven : cuspCount 27 = 6 := by decide
theorem cuspCount_thirtyTwo : cuspCount 32 = 8 := by decide
theorem cuspCount_thirtySix : cuspCount 36 = 12 := by decide
theorem cuspCount_fortyNine : cuspCount 49 = 8 := by decide

section Multiplicativity

theorem gcd_mul_gcd_of_coprime_of_dvd {M N d e : ℕ} (hMN : Nat.Coprime M N)
    (hd : d ∣ M) (he : e ∣ N) :
    Nat.gcd (d * e) (M / d * (N / e)) = Nat.gcd d (M / d) * Nat.gcd e (N / e) := by
  have hde : Nat.Coprime d e :=
    Nat.Coprime.coprime_dvd_left hd (Nat.Coprime.coprime_dvd_right he hMN)
  have hdM' : M / d ∣ M := Nat.div_dvd_of_dvd hd
  have heN' : N / e ∣ N := Nat.div_dvd_of_dvd he
  refine Nat.dvd_antisymm ?_ ?_
  ·
    set h := Nat.gcd (d * e) (M / d * (N / e)) with hh
    have h1 : Nat.gcd h d * Nat.gcd h e = h :=
      (Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime hde).mpr (Nat.gcd_dvd_left _ _)
    rw [← h1]
    refine Nat.mul_dvd_mul ?_ ?_
    ·
      refine Nat.dvd_gcd (Nat.gcd_dvd_right _ _) ?_
      have h2 : Nat.gcd h d ∣ M / d * (N / e) :=
        (Nat.gcd_dvd_left h d).trans (Nat.gcd_dvd_right _ _)
      exact Nat.Coprime.dvd_of_dvd_mul_right
        (Nat.Coprime.coprime_dvd_left ((Nat.gcd_dvd_right h d).trans hd)
          (Nat.Coprime.coprime_dvd_right heN' hMN)) h2
    ·
      refine Nat.dvd_gcd (Nat.gcd_dvd_right _ _) ?_
      have h2 : Nat.gcd h e ∣ M / d * (N / e) :=
        (Nat.gcd_dvd_left h e).trans (Nat.gcd_dvd_right _ _)
      exact Nat.Coprime.dvd_of_dvd_mul_left
        (Nat.Coprime.coprime_dvd_left ((Nat.gcd_dvd_right h e).trans he)
          (Nat.Coprime.coprime_dvd_right hdM' hMN.symm)) h2
  ·
    refine Nat.dvd_gcd ?_ ?_
    · exact Nat.mul_dvd_mul (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_left _ _)
    · exact Nat.mul_dvd_mul (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_right _ _)

theorem cuspCount_mul_of_coprime {M N : ℕ} (hM : M ≠ 0) (hN : N ≠ 0)
    (hMN : Nat.Coprime M N) : cuspCount (M * N) = cuspCount M * cuspCount N := by
  simp only [cuspCount]
  rw [Finset.sum_mul_sum, ← Finset.sum_product']
  refine Finset.sum_nbij' (fun k => (Nat.gcd k M, Nat.gcd k N)) (fun p => p.1 * p.2)
    ?_ ?_ ?_ ?_ ?_
  ·
    intro k hk
    simp only [Finset.mem_product, Nat.mem_divisors]
    exact ⟨⟨Nat.gcd_dvd_right _ _, hM⟩, ⟨Nat.gcd_dvd_right _ _, hN⟩⟩
  ·
    rintro ⟨d, e⟩ hp
    simp only [Finset.mem_product, Nat.mem_divisors] at hp
    exact Nat.mem_divisors.mpr ⟨Nat.mul_dvd_mul hp.1.1 hp.2.1, mul_ne_zero hM hN⟩
  ·
    intro k hk
    rw [Nat.mem_divisors] at hk
    exact (Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime hMN).mpr hk.1
  ·
    rintro ⟨d, e⟩ hp
    simp only [Finset.mem_product, Nat.mem_divisors] at hp
    have h1 : Nat.gcd (d * e) M = d := by
      rw [mul_comm]
      exact Nat.gcd_mul_of_coprime_of_dvd
        (Nat.Coprime.coprime_dvd_left hp.2.1 hMN.symm) hp.1.1
    have h2 : Nat.gcd (d * e) N = e :=
      Nat.gcd_mul_of_coprime_of_dvd (Nat.Coprime.coprime_dvd_left hp.1.1 hMN) hp.2.1
    simp only [h1, h2]
  ·
    intro k hk
    rw [Nat.mem_divisors] at hk
    obtain ⟨hkdvd, -⟩ := hk
    have hd : Nat.gcd k M ∣ M := Nat.gcd_dvd_right _ _
    have he : Nat.gcd k N ∣ N := Nat.gcd_dvd_right _ _
    have hk_eq : Nat.gcd k M * Nat.gcd k N = k :=
      (Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime hMN).mpr hkdvd
    have hquot : M * N / (Nat.gcd k M * Nat.gcd k N) = M / Nat.gcd k M * (N / Nat.gcd k N) :=
      (Nat.div_mul_div_comm hd he).symm
    calc Nat.totient (Nat.gcd k (M * N / k))
        = Nat.totient (Nat.gcd (Nat.gcd k M * Nat.gcd k N)
            (M / Nat.gcd k M * (N / Nat.gcd k N))) := by rw [← hquot, hk_eq]
      _ = Nat.totient (Nat.gcd (Nat.gcd k M) (M / Nat.gcd k M) *
            Nat.gcd (Nat.gcd k N) (N / Nat.gcd k N)) := by
            rw [gcd_mul_gcd_of_coprime_of_dvd hMN hd he]
      _ = _ := Nat.totient_mul (Nat.Coprime.coprime_dvd_left
            ((Nat.gcd_dvd_left _ _).trans hd)
            (Nat.Coprime.coprime_dvd_right ((Nat.gcd_dvd_left _ _).trans he) hMN))

end Multiplicativity
p2m_reactivate "P2MW.S_ModularCurve_genusFormula_isNat.ModularCurve"

namespace CuspSpace

variable {N : ℕ}

end CuspSpace
p2m_reactivate "P2MW.S_ModularCurve_genusFormula_isNat.ModularCurve"

end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_genusFormula_isNat.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "nuTwo nuThree cuspCount cuspCount_one genusFormula dedekindPsi dedekindPsi_one ModularPolynomialData ModularPolynomialData.natDegree_eq cuspCount_prime"
p2m_open "ModularCurve"

theorem dedekindPsi_three : dedekindPsi 3 = 4 := by
  rw [dedekindPsi_prime (by norm_num : Nat.Prime 3)]

theorem dedekindPsi_five : dedekindPsi 5 = 6 := by
  rw [dedekindPsi_prime (by norm_num : Nat.Prime 5)]

theorem dedekindPsi_seven : dedekindPsi 7 = 8 := by
  rw [dedekindPsi_prime (by norm_num : Nat.Prime 7)]

theorem dedekindPsi_eleven : dedekindPsi 11 = 12 := by
  rw [dedekindPsi_prime (by norm_num : Nat.Prime 11)]

theorem dedekindPsi_seventeen : dedekindPsi 17 = 18 := by
  rw [dedekindPsi_prime (by norm_num : Nat.Prime 17)]

theorem dedekindPsi_nineteen : dedekindPsi 19 = 20 := by
  rw [dedekindPsi_prime (by norm_num : Nat.Prime 19)]

theorem dedekindPsi_four : dedekindPsi 4 = 6 := by
  rw [show (4 : ℕ) = 2 ^ 2 by norm_num,
    dedekindPsi_prime_pow 2 2 (by norm_num) (by norm_num)]
  norm_num

theorem dedekindPsi_eight : dedekindPsi 8 = 12 := by
  rw [show (8 : ℕ) = 2 ^ 3 by norm_num,
    dedekindPsi_prime_pow 2 3 (by norm_num) (by norm_num)]
  norm_num

theorem dedekindPsi_nine : dedekindPsi 9 = 12 := by
  rw [show (9 : ℕ) = 3 ^ 2 by norm_num,
    dedekindPsi_prime_pow 3 2 (by norm_num) (by norm_num)]
  norm_num

theorem dedekindPsi_twentySeven : dedekindPsi 27 = 36 := by
  rw [show (27 : ℕ) = 3 ^ 3 by norm_num,
    dedekindPsi_prime_pow 3 3 (by norm_num) (by norm_num)]
  norm_num

theorem dedekindPsi_thirtyTwo : dedekindPsi 32 = 48 := by
  rw [show (32 : ℕ) = 2 ^ 5 by norm_num,
    dedekindPsi_prime_pow 2 5 (by norm_num) (by norm_num)]
  norm_num

theorem dedekindPsi_fortyNine : dedekindPsi 49 = 56 := by
  rw [show (49 : ℕ) = 7 ^ 2 by norm_num,
    dedekindPsi_prime_pow 7 2 (by norm_num) (by norm_num)]
  norm_num

theorem dedekindPsi_six : dedekindPsi 6 = 12 := by
  rw [show (6 : ℕ) = 2 * 3 by norm_num, dedekindPsi_mul_of_coprime 2 3 (by norm_num),
    dedekindPsi_two, dedekindPsi_three]

theorem dedekindPsi_ten : dedekindPsi 10 = 18 := by
  rw [show (10 : ℕ) = 2 * 5 by norm_num, dedekindPsi_mul_of_coprime 2 5 (by norm_num),
    dedekindPsi_two, dedekindPsi_five]

theorem dedekindPsi_twelve : dedekindPsi 12 = 24 := by
  rw [show (12 : ℕ) = 4 * 3 by norm_num, dedekindPsi_mul_of_coprime 4 3 (by norm_num),
    dedekindPsi_four, dedekindPsi_three]

theorem dedekindPsi_fourteen : dedekindPsi 14 = 24 := by
  rw [show (14 : ℕ) = 2 * 7 by norm_num, dedekindPsi_mul_of_coprime 2 7 (by norm_num),
    dedekindPsi_two, dedekindPsi_seven]

theorem dedekindPsi_fifteen : dedekindPsi 15 = 24 := by
  rw [show (15 : ℕ) = 3 * 5 by norm_num, dedekindPsi_mul_of_coprime 3 5 (by norm_num),
    dedekindPsi_three, dedekindPsi_five]

theorem dedekindPsi_twenty : dedekindPsi 20 = 36 := by
  rw [show (20 : ℕ) = 4 * 5 by norm_num, dedekindPsi_mul_of_coprime 4 5 (by norm_num),
    dedekindPsi_four, dedekindPsi_five]

theorem dedekindPsi_twentyOne : dedekindPsi 21 = 32 := by
  rw [show (21 : ℕ) = 3 * 7 by norm_num, dedekindPsi_mul_of_coprime 3 7 (by norm_num),
    dedekindPsi_three, dedekindPsi_seven]

theorem dedekindPsi_twentyFour : dedekindPsi 24 = 48 := by
  rw [show (24 : ℕ) = 8 * 3 by norm_num, dedekindPsi_mul_of_coprime 8 3 (by norm_num),
    dedekindPsi_eight, dedekindPsi_three]

theorem dedekindPsi_thirtySix : dedekindPsi 36 = 72 := by
  rw [show (36 : ℕ) = 4 * 9 by norm_num, dedekindPsi_mul_of_coprime 4 9 (by norm_num),
    dedekindPsi_four, dedekindPsi_nine]

def genusOneLevels : List ℕ := [11, 14, 15, 17, 19, 20, 21, 24, 27, 32, 36, 49]

end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_genusFormula_isNat.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "nuTwo nuThree cuspCount cuspCount_one genusFormula dedekindPsi dedekindPsi_one ModularPolynomialData ModularPolynomialData.natDegree_eq cuspCount_prime"
p2m_open "ModularCurve"

theorem twelve_mul_genusFormula (N : ℕ) :
    12 * genusFormula N
      = 12 + (dedekindPsi N : ℚ) - 3 * (nuTwo N : ℚ) - 4 * (nuThree N : ℚ)
        - 6 * (cuspCount N : ℚ) := by
  unfold genusFormula
  ring

theorem dedekindPsi_thirteen : dedekindPsi 13 = 14 := by
  rw [dedekindPsi_prime (by norm_num : Nat.Prime 13)]

theorem dedekindPsi_sixteen : dedekindPsi 16 = 24 := by
  rw [show (16 : ℕ) = 2 ^ 4 by norm_num,
    dedekindPsi_prime_pow 2 4 (by norm_num) (by norm_num)]
  norm_num

theorem dedekindPsi_eighteen : dedekindPsi 18 = 36 := by
  rw [show (18 : ℕ) = 2 * 9 by norm_num, dedekindPsi_mul_of_coprime 2 9 (by norm_num),
    dedekindPsi_two, dedekindPsi_nine]

theorem dedekindPsi_twentyFive : dedekindPsi 25 = 30 := by
  rw [show (25 : ℕ) = 5 ^ 2 by norm_num,
    dedekindPsi_prime_pow 5 2 (by norm_num) (by norm_num)]
  norm_num

private theorem nuTwo_eq_of_card_GenusTab {N : ℕ} [NeZero N] {v : ℕ}
    (h : Fintype.card {x : ZMod N // x ^ 2 + 1 = 0} = v) : nuTwo N = v := by
  have hcard : nuTwo N = Fintype.card {x : ZMod N // x ^ 2 + 1 = 0} :=
    Nat.card_eq_fintype_card
  rw [hcard, h]

theorem nuTwo_three : nuTwo 3 = 0 := nuTwo_eq_of_card_GenusTab (by decide)
theorem nuTwo_four : nuTwo 4 = 0 := nuTwo_eq_of_card_GenusTab (by decide)
theorem nuTwo_six : nuTwo 6 = 0 := nuTwo_eq_of_card_GenusTab (by decide)
theorem nuTwo_seven : nuTwo 7 = 0 := nuTwo_eq_of_card_GenusTab (by decide)
theorem nuTwo_eight : nuTwo 8 = 0 := nuTwo_eq_of_card_GenusTab (by decide)
theorem nuTwo_nine : nuTwo 9 = 0 := nuTwo_eq_of_card_GenusTab (by decide)
theorem nuTwo_ten : nuTwo 10 = 2 := nuTwo_eq_of_card_GenusTab (by decide)
theorem nuTwo_twelve : nuTwo 12 = 0 := nuTwo_eq_of_card_GenusTab (by decide)
theorem nuTwo_fourteen : nuTwo 14 = 0 := nuTwo_eq_of_card_GenusTab (by decide)
theorem nuTwo_fifteen : nuTwo 15 = 0 := nuTwo_eq_of_card_GenusTab (by decide)
theorem nuTwo_sixteen : nuTwo 16 = 0 := nuTwo_eq_of_card_GenusTab (by decide)
theorem nuTwo_seventeen : nuTwo 17 = 2 := nuTwo_eq_of_card_GenusTab (by decide)
theorem nuTwo_eighteen : nuTwo 18 = 0 := nuTwo_eq_of_card_GenusTab (by decide)
theorem nuTwo_nineteen : nuTwo 19 = 0 := nuTwo_eq_of_card_GenusTab (by decide)
theorem nuTwo_twenty : nuTwo 20 = 0 := nuTwo_eq_of_card_GenusTab (by decide)
theorem nuTwo_twentyOne : nuTwo 21 = 0 := nuTwo_eq_of_card_GenusTab (by decide)
theorem nuTwo_twentyFour : nuTwo 24 = 0 := nuTwo_eq_of_card_GenusTab (by decide)
theorem nuTwo_twentyFive : nuTwo 25 = 2 := nuTwo_eq_of_card_GenusTab (by decide)
theorem nuTwo_twentySeven : nuTwo 27 = 0 := nuTwo_eq_of_card_GenusTab (by decide)
theorem nuTwo_thirtyTwo : nuTwo 32 = 0 := nuTwo_eq_of_card_GenusTab (by decide)
theorem nuTwo_thirtySix : nuTwo 36 = 0 := nuTwo_eq_of_card_GenusTab (by decide)
theorem nuTwo_fortyNine : nuTwo 49 = 0 := nuTwo_eq_of_card_GenusTab (by decide)

private theorem nuThree_eq_of_card_GenusTab {N : ℕ} [NeZero N] {v : ℕ}
    (h : Fintype.card {x : ZMod N // x ^ 2 + x + 1 = 0} = v) : nuThree N = v := by
  have hcard : nuThree N = Fintype.card {x : ZMod N // x ^ 2 + x + 1 = 0} :=
    Nat.card_eq_fintype_card
  rw [hcard, h]

theorem nuThree_two : nuThree 2 = 0 := nuThree_eq_of_card_GenusTab (by decide)
theorem nuThree_four : nuThree 4 = 0 := nuThree_eq_of_card_GenusTab (by decide)
theorem nuThree_five : nuThree 5 = 0 := nuThree_eq_of_card_GenusTab (by decide)
theorem nuThree_six : nuThree 6 = 0 := nuThree_eq_of_card_GenusTab (by decide)
theorem nuThree_eight : nuThree 8 = 0 := nuThree_eq_of_card_GenusTab (by decide)
theorem nuThree_nine : nuThree 9 = 0 := nuThree_eq_of_card_GenusTab (by decide)
theorem nuThree_ten : nuThree 10 = 0 := nuThree_eq_of_card_GenusTab (by decide)
theorem nuThree_twelve : nuThree 12 = 0 := nuThree_eq_of_card_GenusTab (by decide)
theorem nuThree_fourteen : nuThree 14 = 0 := nuThree_eq_of_card_GenusTab (by decide)
theorem nuThree_fifteen : nuThree 15 = 0 := nuThree_eq_of_card_GenusTab (by decide)
theorem nuThree_sixteen : nuThree 16 = 0 := nuThree_eq_of_card_GenusTab (by decide)
theorem nuThree_seventeen : nuThree 17 = 0 := nuThree_eq_of_card_GenusTab (by decide)
theorem nuThree_eighteen : nuThree 18 = 0 := nuThree_eq_of_card_GenusTab (by decide)
theorem nuThree_twenty : nuThree 20 = 0 := nuThree_eq_of_card_GenusTab (by decide)
theorem nuThree_twentyOne : nuThree 21 = 2 := nuThree_eq_of_card_GenusTab (by decide)
theorem nuThree_twentyFour : nuThree 24 = 0 := nuThree_eq_of_card_GenusTab (by decide)
theorem nuThree_twentyFive : nuThree 25 = 0 := nuThree_eq_of_card_GenusTab (by decide)
theorem nuThree_twentySeven : nuThree 27 = 0 := nuThree_eq_of_card_GenusTab (by decide)
theorem nuThree_thirtyTwo : nuThree 32 = 0 := nuThree_eq_of_card_GenusTab (by decide)
theorem nuThree_thirtySix : nuThree 36 = 0 := nuThree_eq_of_card_GenusTab (by decide)
theorem nuThree_fortyNine : nuThree 49 = 2 := nuThree_eq_of_card_GenusTab (by decide)

theorem cuspCount_five : cuspCount 5 = 2 := cuspCount_prime (by norm_num)
theorem cuspCount_six : cuspCount 6 = 4 := by decide
theorem cuspCount_seven : cuspCount 7 = 2 := cuspCount_prime (by norm_num)
theorem cuspCount_eight : cuspCount 8 = 4 := by decide
theorem cuspCount_ten : cuspCount 10 = 4 := by decide
theorem cuspCount_twelve : cuspCount 12 = 6 := by decide
theorem cuspCount_thirteen : cuspCount 13 = 2 := cuspCount_prime (by norm_num)
theorem cuspCount_sixteen : cuspCount 16 = 6 := by decide
theorem cuspCount_eighteen : cuspCount 18 = 8 := by decide
theorem cuspCount_twentyFive : cuspCount 25 = 6 := by decide

theorem genusFormula_one : genusFormula 1 = 0 := by
  unfold genusFormula
  rw [dedekindPsi_one, nuTwo_one, nuThree_one, cuspCount_one]
  norm_num

theorem genusFormula_two : genusFormula 2 = 0 := by
  unfold genusFormula
  rw [dedekindPsi_two, nuTwo_two, nuThree_two, cuspCount_two]
  norm_num

theorem genusFormula_three : genusFormula 3 = 0 := by
  unfold genusFormula
  rw [dedekindPsi_three, nuTwo_three, nuThree_three, cuspCount_three]
  norm_num

theorem genusFormula_four : genusFormula 4 = 0 := by
  unfold genusFormula
  rw [dedekindPsi_four, nuTwo_four, nuThree_four, cuspCount_four]
  norm_num

theorem genusFormula_five : genusFormula 5 = 0 := by
  unfold genusFormula
  rw [dedekindPsi_five, nuTwo_five, nuThree_five, cuspCount_five]
  norm_num

theorem genusFormula_six : genusFormula 6 = 0 := by
  unfold genusFormula
  rw [dedekindPsi_six, nuTwo_six, nuThree_six, cuspCount_six]
  norm_num

theorem genusFormula_seven : genusFormula 7 = 0 := by
  unfold genusFormula
  rw [dedekindPsi_seven, nuTwo_seven, nuThree_seven, cuspCount_seven]
  norm_num

theorem genusFormula_eight : genusFormula 8 = 0 := by
  unfold genusFormula
  rw [dedekindPsi_eight, nuTwo_eight, nuThree_eight, cuspCount_eight]
  norm_num

theorem genusFormula_nine : genusFormula 9 = 0 := by
  unfold genusFormula
  rw [dedekindPsi_nine, nuTwo_nine, nuThree_nine, cuspCount_nine]
  norm_num

theorem genusFormula_ten : genusFormula 10 = 0 := by
  unfold genusFormula
  rw [dedekindPsi_ten, nuTwo_ten, nuThree_ten, cuspCount_ten]
  norm_num

theorem genusFormula_twelve : genusFormula 12 = 0 := by
  unfold genusFormula
  rw [dedekindPsi_twelve, nuTwo_twelve, nuThree_twelve, cuspCount_twelve]
  norm_num

theorem genusFormula_thirteen : genusFormula 13 = 0 := by
  unfold genusFormula
  rw [dedekindPsi_thirteen, nuTwo_thirteen, nuThree_thirteen, cuspCount_thirteen]
  norm_num

theorem genusFormula_sixteen : genusFormula 16 = 0 := by
  unfold genusFormula
  rw [dedekindPsi_sixteen, nuTwo_sixteen, nuThree_sixteen, cuspCount_sixteen]
  norm_num

theorem genusFormula_eighteen : genusFormula 18 = 0 := by
  unfold genusFormula
  rw [dedekindPsi_eighteen, nuTwo_eighteen, nuThree_eighteen, cuspCount_eighteen]
  norm_num

theorem genusFormula_twentyFive : genusFormula 25 = 0 := by
  unfold genusFormula
  rw [dedekindPsi_twentyFive, nuTwo_twentyFive, nuThree_twentyFive, cuspCount_twentyFive]
  norm_num

theorem genusFormula_eleven : genusFormula 11 = 1 := by
  unfold genusFormula
  rw [dedekindPsi_eleven, nuTwo_eleven, nuThree_eleven, cuspCount_eleven]
  norm_num

theorem genusFormula_fourteen : genusFormula 14 = 1 := by
  unfold genusFormula
  rw [dedekindPsi_fourteen, nuTwo_fourteen, nuThree_fourteen, cuspCount_fourteen]
  norm_num

theorem genusFormula_fifteen : genusFormula 15 = 1 := by
  unfold genusFormula
  rw [dedekindPsi_fifteen, nuTwo_fifteen, nuThree_fifteen, cuspCount_fifteen]
  norm_num

theorem genusFormula_seventeen : genusFormula 17 = 1 := by
  unfold genusFormula
  rw [dedekindPsi_seventeen, nuTwo_seventeen, nuThree_seventeen, cuspCount_seventeen]
  norm_num

theorem genusFormula_nineteen : genusFormula 19 = 1 := by
  unfold genusFormula
  rw [dedekindPsi_nineteen, nuTwo_nineteen, nuThree_nineteen, cuspCount_nineteen]
  norm_num

theorem genusFormula_twenty : genusFormula 20 = 1 := by
  unfold genusFormula
  rw [dedekindPsi_twenty, nuTwo_twenty, nuThree_twenty, cuspCount_twenty]
  norm_num

theorem genusFormula_twentyOne : genusFormula 21 = 1 := by
  unfold genusFormula
  rw [dedekindPsi_twentyOne, nuTwo_twentyOne, nuThree_twentyOne, cuspCount_twentyOne]
  norm_num

theorem genusFormula_twentyFour : genusFormula 24 = 1 := by
  unfold genusFormula
  rw [dedekindPsi_twentyFour, nuTwo_twentyFour, nuThree_twentyFour, cuspCount_twentyFour]
  norm_num

theorem genusFormula_twentySeven : genusFormula 27 = 1 := by
  unfold genusFormula
  rw [dedekindPsi_twentySeven, nuTwo_twentySeven, nuThree_twentySeven,
    cuspCount_twentySeven]
  norm_num

theorem genusFormula_thirtyTwo : genusFormula 32 = 1 := by
  unfold genusFormula
  rw [dedekindPsi_thirtyTwo, nuTwo_thirtyTwo, nuThree_thirtyTwo, cuspCount_thirtyTwo]
  norm_num

theorem genusFormula_thirtySix : genusFormula 36 = 1 := by
  unfold genusFormula
  rw [dedekindPsi_thirtySix, nuTwo_thirtySix, nuThree_thirtySix, cuspCount_thirtySix]
  norm_num

theorem genusFormula_fortyNine : genusFormula 49 = 1 := by
  unfold genusFormula
  rw [dedekindPsi_fortyNine, nuTwo_fortyNine, nuThree_fortyNine, cuspCount_fortyNine]
  norm_num

def genusZeroLevels : List ℕ := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 13, 16, 18, 25]

theorem genusFormula_genusZeroLevels : genusZeroLevels.map genusFormula
    = List.replicate 15 0 := by
  simp only [genusZeroLevels, List.map_cons, List.map_nil, genusFormula_one,
    genusFormula_two, genusFormula_three, genusFormula_four, genusFormula_five,
    genusFormula_six, genusFormula_seven, genusFormula_eight, genusFormula_nine,
    genusFormula_ten, genusFormula_twelve, genusFormula_thirteen, genusFormula_sixteen,
    genusFormula_eighteen, genusFormula_twentyFive]
  rfl

theorem genusFormula_genusOneLevels : genusOneLevels.map genusFormula
    = List.replicate 12 1 := by
  simp only [genusOneLevels, List.map_cons, List.map_nil, genusFormula_eleven,
    genusFormula_fourteen, genusFormula_fifteen, genusFormula_seventeen,
    genusFormula_nineteen, genusFormula_twenty, genusFormula_twentyOne,
    genusFormula_twentyFour, genusFormula_twentySeven, genusFormula_thirtyTwo,
    genusFormula_thirtySix, genusFormula_fortyNine]
  rfl

end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_genusFormula_isNat.ModularCurve"

set_option autoImplicit false

namespace ModularCurve
p2m_export "ModularCurve" "nuTwo nuThree cuspCount cuspCount_one genusFormula dedekindPsi dedekindPsi_one ModularPolynomialData ModularPolynomialData.natDegree_eq cuspCount_prime"
p2m_open "ModularCurve"

open Finset

theorem squarefree_iff_forall_Icc {d : ℕ} (hd : d ≠ 0) :
    Squarefree d ↔ ∀ m ∈ Finset.Icc 2 d, ¬ m * m ∣ d := by
  constructor
  · intro hsq m hm hmm
    rw [Finset.mem_Icc] at hm
    exact absurd (Nat.isUnit_iff.mp (hsq m hmm)) (by omega)
  · intro h x hx
    rw [Nat.isUnit_iff]
    rcases Nat.lt_or_ge x 2 with hx2 | hx2
    · interval_cases x
      · exact absurd (Nat.eq_zero_of_zero_dvd (by simpa using hx)) hd
      · rfl
    · exact absurd hx (h x (Finset.mem_Icc.mpr
        ⟨hx2, le_trans (Nat.le_mul_of_pos_left x (by omega)) (Nat.le_of_dvd (by omega) hx)⟩))

def squarefreeFin (d : ℕ) : Prop := ∀ m ∈ Finset.Icc 2 d, ¬ m * m ∣ d

scoped instance (d : ℕ) : Decidable (squarefreeFin d) := Finset.decidableDforallFinset

def dedekindPsiFin (N : ℕ) : ℕ :=
  ∑ d ∈ N.divisors with squarefreeFin d, N / d

theorem dedekindPsiFin_eq (N : ℕ) : dedekindPsiFin N = dedekindPsi N := by
  unfold dedekindPsiFin dedekindPsi
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  refine Finset.filter_congr (fun d hd => ?_)
  exact (squarefree_iff_forall_Icc (Nat.pos_of_mem_divisors hd).ne').symm

def nuTwoFin (N : ℕ) : ℕ :=
  ((Finset.range N).filter fun x => (x ^ 2 + 1) % N = 0).card

def nuThreeFin (N : ℕ) : ℕ :=
  ((Finset.range N).filter fun x => (x ^ 2 + x + 1) % N = 0).card

private theorem zmod_poly2_eq_zero_iff_GenusOne {N : ℕ} (x : ℕ) :
    ((x : ZMod N) ^ 2 + 1 = 0) ↔ N ∣ (x ^ 2 + 1) := by
  rw [show ((x : ZMod N) ^ 2 + 1 : ZMod N) = ((x ^ 2 + 1 : ℕ) : ZMod N) by push_cast; ring,
    ZMod.natCast_eq_zero_iff]

private theorem zmod_poly3_eq_zero_iff_GenusOne {N : ℕ} (x : ℕ) :
    ((x : ZMod N) ^ 2 + (x : ZMod N) + 1 = 0) ↔ N ∣ (x ^ 2 + x + 1) := by
  rw [show ((x : ZMod N) ^ 2 + (x : ZMod N) + 1 : ZMod N) = ((x ^ 2 + x + 1 : ℕ) : ZMod N) by
    push_cast; ring, ZMod.natCast_eq_zero_iff]

theorem nuTwoFin_eq {N : ℕ} (hN : N ≠ 0) : nuTwoFin N = nuTwo N := by
  haveI : NeZero N := ⟨hN⟩
  unfold nuTwoFin nuTwo
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  refine Finset.card_bij' (fun x _ => (x : ZMod N)) (fun y _ => ZMod.val y) ?_ ?_ ?_ ?_
  · intro x hx
    rw [Finset.mem_filter, Finset.mem_range] at hx
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, (zmod_poly2_eq_zero_iff_GenusOne x).mpr (Nat.dvd_of_mod_eq_zero hx.2)⟩
  · intro y hy
    rw [Finset.mem_filter] at hy
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (ZMod.val_lt y), ?_⟩
    show (ZMod.val y ^ 2 + 1) % N = 0
    obtain ⟨c, hc⟩ := (zmod_poly2_eq_zero_iff_GenusOne (ZMod.val y)).mp
      (by rw [ZMod.natCast_zmod_val]; exact hy.2)
    simp [hc]
  · intro x hx
    rw [Finset.mem_filter, Finset.mem_range] at hx
    exact ZMod.val_natCast_of_lt hx.1
  · intro y _
    exact ZMod.natCast_zmod_val y

theorem nuThreeFin_eq {N : ℕ} (hN : N ≠ 0) : nuThreeFin N = nuThree N := by
  haveI : NeZero N := ⟨hN⟩
  unfold nuThreeFin nuThree
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  refine Finset.card_bij' (fun x _ => (x : ZMod N)) (fun y _ => ZMod.val y) ?_ ?_ ?_ ?_
  · intro x hx
    rw [Finset.mem_filter, Finset.mem_range] at hx
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, (zmod_poly3_eq_zero_iff_GenusOne x).mpr (Nat.dvd_of_mod_eq_zero hx.2)⟩
  · intro y hy
    rw [Finset.mem_filter] at hy
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (ZMod.val_lt y), ?_⟩
    show (ZMod.val y ^ 2 + ZMod.val y + 1) % N = 0
    obtain ⟨c, hc⟩ := (zmod_poly3_eq_zero_iff_GenusOne (ZMod.val y)).mp
      (by rw [ZMod.natCast_zmod_val]; exact hy.2)
    simp [hc]
  · intro x hx
    rw [Finset.mem_filter, Finset.mem_range] at hx
    exact ZMod.val_natCast_of_lt hx.1
  · intro y _
    exact ZMod.natCast_zmod_val y

def genusFormulaNum (N : ℕ) : ℤ :=
  12 + (dedekindPsiFin N : ℤ) - 3 * (nuTwoFin N : ℤ) - 4 * (nuThreeFin N : ℤ)
    - 6 * (cuspCount N : ℤ)

theorem genusFormulaNum_cast {N : ℕ} (hN : N ≠ 0) :
    (genusFormulaNum N : ℚ) = 12 * genusFormula N := by
  rw [genusFormulaNum, twelve_mul_genusFormula, dedekindPsiFin_eq,
    nuTwoFin_eq hN, nuThreeFin_eq hN]
  push_cast
  ring

theorem genusFormula_eq_one_iff_genusFormulaNum {M : ℕ} (hM : M ≠ 0) :
    genusFormula M = 1 ↔ genusFormulaNum M = 12 := by
  constructor
  · intro h
    have hcast : (genusFormulaNum M : ℚ) = 12 := by
      rw [genusFormulaNum_cast hM, h]; norm_num
    exact_mod_cast hcast
  · intro h
    have hcast : (12 : ℚ) * genusFormula M = 12 := by
      rw [← genusFormulaNum_cast hM, h]; norm_num
    linarith

def PsiGrowthBound (M : ℕ) : Prop :=
  (dedekindPsi M : ℚ) / 12
    > (nuTwo M : ℚ) / 4 + (nuThree M : ℚ) / 3 + (cuspCount M : ℚ) / 2

theorem one_lt_genusFormula_iff_psiGrowthBound (M : ℕ) :
    1 < genusFormula M ↔ PsiGrowthBound M := by
  unfold PsiGrowthBound genusFormula
  constructor <;> intro h <;> linarith

theorem one_lt_genusFormula_of_psiGrowthBound {M : ℕ} (h : PsiGrowthBound M) :
    1 < genusFormula M :=
  (one_lt_genusFormula_iff_psiGrowthBound M).mpr h

theorem psiGrowthBound_iff_lt_genusFormulaNum {M : ℕ} (hM : M ≠ 0) :
    PsiGrowthBound M ↔ 12 < genusFormulaNum M := by
  rw [← one_lt_genusFormula_iff_psiGrowthBound]
  rw [show (12 : ℤ) < genusFormulaNum M ↔ (12 : ℚ) < (genusFormulaNum M : ℚ) by
    exact_mod_cast Iff.rfl]
  rw [genusFormulaNum_cast hM]
  constructor <;> intro h <;> linarith

theorem genusFormulaNum_eq_twelve_iff_mem_of_le_fortyNine :
    ∀ M ∈ Finset.Ico 1 50, (genusFormulaNum M = 12 ↔ M ∈ genusOneLevels) := by
  decide

theorem genusFormula_eq_one_iff_mem_of_le_fortyNine {M : ℕ}
    (h1 : 1 ≤ M) (h49 : M ≤ 49) :
    genusFormula M = 1 ↔ M ∈ genusOneLevels := by
  rw [genusFormula_eq_one_iff_genusFormulaNum (by omega)]
  exact genusFormulaNum_eq_twelve_iff_mem_of_le_fortyNine M
    (Finset.mem_Ico.mpr ⟨h1, by omega⟩)

theorem twelve_lt_genusFormulaNum_of_le_fortyNine_of_notMem :
    ∀ M ∈ Finset.Ico 1 50,
      M ∉ genusZeroLevels → M ∉ genusOneLevels → 12 < genusFormulaNum M := by
  decide

theorem nuTwo_prime_le_two {p : ℕ} (hp : p.Prime) : nuTwo p ≤ 2 := by
  rcases eq_or_ne p 2 with rfl | hp2
  · rw [nuTwo_two]; omega
  · rw [nuTwo_prime hp hp2]; split_ifs <;> omega

theorem nuThree_prime_le_two {p : ℕ} (hp : p.Prime) : nuThree p ≤ 2 := by
  rcases eq_or_ne p 3 with rfl | hp3
  · rw [nuThree_three]; omega
  · rw [nuThree_prime hp hp3]; split_ifs <;> omega

theorem psiGrowthBound_of_prime_of_lt {p : ℕ} (hp : p.Prime) (hp25 : 25 < p) :
    PsiGrowthBound p := by
  rw [psiGrowthBound_iff_lt_genusFormulaNum hp.pos.ne']
  have hψ : dedekindPsiFin p = p + 1 := by rw [dedekindPsiFin_eq, dedekindPsi_prime hp]
  have hν2 : (nuTwoFin p : ℤ) ≤ 2 := by
    rw [nuTwoFin_eq hp.pos.ne']; exact_mod_cast nuTwo_prime_le_two hp
  have hν3 : (nuThreeFin p : ℤ) ≤ 2 := by
    rw [nuThreeFin_eq hp.pos.ne']; exact_mod_cast nuThree_prime_le_two hp
  have hcusp : cuspCount p = 2 := cuspCount_prime hp
  unfold genusFormulaNum
  rw [hψ, hcusp]
  have hpcast : (25 : ℤ) < (p : ℤ) := by exact_mod_cast hp25
  push_cast
  linarith

theorem genusFormula_eq_one_iff_mem_genusOneLevels {M : ℕ} (hM : 0 < M)
    (hgrowth : 49 < M → PsiGrowthBound M) :
    genusFormula M = 1 ↔ M ∈ genusOneLevels := by
  rcases le_or_gt M 49 with h49 | h49
  · exact genusFormula_eq_one_iff_mem_of_le_fortyNine hM h49
  · constructor
    · intro h1
      exact absurd h1 (one_lt_genusFormula_of_psiGrowthBound (hgrowth h49)).ne'
    · intro hmem

      exfalso
      have hle49 : M ≤ 49 := by
        have hall : ∀ M ∈ genusOneLevels, M ≤ 49 := by decide
        exact hall M hmem
      omega

end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_genusFormula_isNat.ModularCurve"

set_option autoImplicit false

namespace ModularCurve
p2m_export "ModularCurve" "nuTwo nuThree cuspCount cuspCount_one genusFormula dedekindPsi dedekindPsi_one ModularPolynomialData ModularPolynomialData.natDegree_eq cuspCount_prime"
p2m_open "ModularCurve"

open Finset

section HenselFree

variable {p k : ℕ}

theorem ZMod.isUnit_iff_castHom_ne_zero (hp : p.Prime) (hk : 0 < k) (u : ZMod (p ^ k)) :
    IsUnit u ↔ ZMod.castHom (dvd_pow_self p hk.ne') (ZMod p) u ≠ 0 := by
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero k hp.pos.ne'⟩
  have hcast : ZMod.castHom (dvd_pow_self p hk.ne') (ZMod p) u = (u.val : ZMod p) := by
    conv_lhs => rw [← ZMod.natCast_zmod_val u]; simp only [map_natCast]
  rw [hcast, Ne, ZMod.natCast_eq_zero_iff, ← hp.coprime_iff_not_dvd, Nat.coprime_comm,
    ← Nat.coprime_pow_right_iff hk, ← ZMod.isUnit_iff_coprime, ZMod.natCast_zmod_val]

private theorem castHom_sq_add_one_PsiGrowt {p k : ℕ} (hk : 0 < k) {x : ZMod (p ^ k)}
    (hx : x ^ 2 + 1 = 0) :
    (ZMod.castHom (dvd_pow_self p hk.ne') (ZMod p) x) ^ 2 + 1 = 0 := by
  have h := congrArg (ZMod.castHom (dvd_pow_self p hk.ne') (ZMod p)) hx
  simpa only [map_add, map_pow, map_one, map_zero] using h

theorem nuTwo_prime_pow_le_nuTwo_prime (hp : p.Prime) (hp2 : p ≠ 2) (hk : 0 < k) :
    nuTwo (p ^ k) ≤ nuTwo p := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero k hp.pos.ne'⟩
  unfold nuTwo
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  refine Fintype.card_le_of_injective
    (fun z => ⟨ZMod.castHom (dvd_pow_self p hk.ne') (ZMod p) z.1,
      castHom_sq_add_one_PsiGrowt hk z.2⟩) ?_
  rintro ⟨x, hx⟩ ⟨y, hy⟩ heq
  simp only [Subtype.mk.injEq] at heq ⊢
  set f := ZMod.castHom (dvd_pow_self p hk.ne') (ZMod p)

  have hprod : (x - y) * (x + y) = 0 := by linear_combination hx - hy

  have hxne : f x ≠ 0 := ne_zero_of_sq_add_one_eq_zero hp (castHom_sq_add_one_PsiGrowt hk hx)
  have hsum_ne : f (x + y) ≠ 0 := by
    rw [map_add, ← heq, ← two_mul]
    have h2u : (2 : ZMod p) ≠ 0 := by
      have : ((2 : ℕ) : ZMod p) ≠ 0 := fun h =>
        hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
          ((ZMod.natCast_eq_zero_iff 2 p).mp h))
      exact_mod_cast this
    exact mul_ne_zero h2u hxne

  obtain ⟨u, hu⟩ := (ZMod.isUnit_iff_castHom_ne_zero hp hk (x + y)).mpr hsum_ne
  have hxy : x - y = 0 := by
    have := congrArg (· * (↑u⁻¹ : ZMod (p ^ k))) hprod
    simpa [mul_assoc, ← hu] using this
  exact sub_eq_zero.mp hxy

theorem nuTwo_prime_pow_le_two (hp : p.Prime) (hk : 0 < k) : nuTwo (p ^ k) ≤ 2 := by
  rcases eq_or_ne p 2 with rfl | hp2
  · rcases Nat.lt_or_ge k 2 with hk1 | hk2
    · interval_cases k
      rw [pow_one, nuTwo_two]; omega
    · have h4 : (4 : ℕ) ∣ 2 ^ k := by
        have : (2 : ℕ) ^ 2 ∣ 2 ^ k := pow_dvd_pow 2 hk2
        simpa using this
      rw [nuTwo_eq_zero_of_four_dvd h4]; omega
  · exact (nuTwo_prime_pow_le_nuTwo_prime hp hp2 hk).trans (nuTwo_prime_le_two hp)

private theorem castHom_sq_add_self_add_one_PsiGrowt {p k : ℕ} (hk : 0 < k) {x : ZMod (p ^ k)}
    (hx : x ^ 2 + x + 1 = 0) :
    (ZMod.castHom (dvd_pow_self p hk.ne') (ZMod p) x) ^ 2
      + ZMod.castHom (dvd_pow_self p hk.ne') (ZMod p) x + 1 = 0 := by
  have h := congrArg (ZMod.castHom (dvd_pow_self p hk.ne') (ZMod p)) hx
  simpa only [map_add, map_pow, map_one, map_zero] using h

theorem nuThree_prime_pow_le_nuThree_prime (hp : p.Prime) (hp3 : p ≠ 3) (hk : 0 < k) :
    nuThree (p ^ k) ≤ nuThree p := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero k hp.pos.ne'⟩
  unfold nuThree
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  refine Fintype.card_le_of_injective
    (fun z => ⟨ZMod.castHom (dvd_pow_self p hk.ne') (ZMod p) z.1,
      castHom_sq_add_self_add_one_PsiGrowt hk z.2⟩) ?_
  rintro ⟨x, hx⟩ ⟨y, hy⟩ heq
  simp only [Subtype.mk.injEq] at heq ⊢
  set f := ZMod.castHom (dvd_pow_self p hk.ne') (ZMod p)

  have hprod : (x - y) * (x + y + 1) = 0 := by linear_combination hx - hy

  have hxp : f x ^ 2 + f x + 1 = 0 := castHom_sq_add_self_add_one_PsiGrowt hk hx
  have hsum_ne : f (x + y + 1) ≠ 0 := by
    rw [map_add, map_add, map_one, ← heq]
    intro hcon
    have h3 : (3 : ZMod p) = 0 := by
      linear_combination 4 * hxp - (2 * f x + 1) * hcon
    have hcast : ((3 : ℕ) : ZMod p) = 0 := by exact_mod_cast h3
    exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp
      ((ZMod.natCast_eq_zero_iff 3 p).mp hcast))
  obtain ⟨u, hu⟩ := (ZMod.isUnit_iff_castHom_ne_zero hp hk (x + y + 1)).mpr hsum_ne
  have hxy : x - y = 0 := by
    have := congrArg (· * (↑u⁻¹ : ZMod (p ^ k))) hprod
    simpa [mul_assoc, ← hu] using this
  exact sub_eq_zero.mp hxy

theorem nuThree_prime_pow_le_two (hp : p.Prime) (hk : 0 < k) : nuThree (p ^ k) ≤ 2 := by
  rcases eq_or_ne p 3 with rfl | hp3
  · rcases Nat.lt_or_ge k 2 with hk1 | hk2
    · interval_cases k; rw [pow_one, nuThree_three]; omega
    · have h9 : (9 : ℕ) ∣ 3 ^ k := by
        have : (3 : ℕ) ^ 2 ∣ 3 ^ k := pow_dvd_pow 3 hk2
        simpa using this
      rw [nuThree_eq_zero_of_nine_dvd h9]; omega
  · exact (nuThree_prime_pow_le_nuThree_prime hp hp3 hk).trans (nuThree_prime_le_two hp)

end HenselFree
p2m_reactivate "P2MW.S_ModularCurve_genusFormula_isNat.ModularCurve"

section CuspCountPrimePow

variable {p : ℕ}

theorem gcd_pow_pow_eq_pow_min (p a b : ℕ) :
    Nat.gcd (p ^ a) (p ^ b) = p ^ min a b := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, Nat.gcd_eq_left (pow_dvd_pow p h)]
  · rw [min_eq_right h, Nat.gcd_eq_right (pow_dvd_pow p h)]

theorem sum_totient_pow_range (hp : p.Prime) (m : ℕ) :
    ∑ j ∈ Finset.range (m + 1), Nat.totient (p ^ j) = p ^ m := by
  have h := Nat.sum_totient (p ^ m)
  rwa [Nat.sum_divisors_prime_pow hp] at h

theorem cuspCount_prime_pow (hp : p.Prime) {k : ℕ} (hk : 0 < k) :
    cuspCount (p ^ k) = p ^ (k / 2) + p ^ ((k - 1) / 2) := by

  rw [cuspCount, Nat.sum_divisors_prime_pow hp]
  have hsummand : ∀ j ∈ Finset.range (k + 1),
      Nat.totient (Nat.gcd (p ^ j) (p ^ k / p ^ j)) = Nat.totient (p ^ min j (k - j)) := by
    intro j hj
    rw [Finset.mem_range] at hj
    rw [Nat.pow_div (by omega) hp.pos, gcd_pow_pow_eq_pow_min]
  rw [Finset.sum_congr rfl hsummand]

  rw [show k + 1 = (k / 2 + 1) + (k - k / 2) by omega, Finset.sum_range_add]
  have hfirst : ∑ j ∈ Finset.range (k / 2 + 1), Nat.totient (p ^ min j (k - j))
      = p ^ (k / 2) := by
    rw [← sum_totient_pow_range hp (k / 2)]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [Finset.mem_range] at hj
    rw [show min j (k - j) = j from by omega]
  have hsecond : ∑ j ∈ Finset.range (k - k / 2),
        Nat.totient (p ^ min (k / 2 + 1 + j) (k - (k / 2 + 1 + j)))
      = p ^ ((k - 1) / 2) := by
    have hrange : k - k / 2 = (k - 1) / 2 + 1 := by omega
    rw [hrange, ← sum_totient_pow_range hp ((k - 1) / 2), ← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [Finset.mem_range] at hj
    have hmin : min (k / 2 + 1 + ((k - 1) / 2 + 1 - 1 - j))
        (k - (k / 2 + 1 + ((k - 1) / 2 + 1 - 1 - j))) = j := by omega
    rw [hmin]
  rw [hfirst, hsecond]

end CuspCountPrimePow
p2m_reactivate "P2MW.S_ModularCurve_genusFormula_isNat.ModularCurve"

section NuLeBounds

theorem nuTwo_le_self {N : ℕ} (hN : N ≠ 0) : nuTwo N ≤ N := by
  haveI : NeZero N := ⟨hN⟩
  rw [← nuTwoFin_eq hN]
  exact (Finset.card_filter_le _ _).trans (by rw [Finset.card_range])

theorem nuThree_le_self {N : ℕ} (hN : N ≠ 0) : nuThree N ≤ N := by
  haveI : NeZero N := ⟨hN⟩
  rw [← nuThreeFin_eq hN]
  exact (Finset.card_filter_le _ _).trans (by rw [Finset.card_range])

theorem cuspCount_le_self (N : ℕ) : cuspCount N ≤ N := by
  rcases eq_or_ne N 0 with rfl | hN
  · simp [cuspCount]
  calc cuspCount N ≤ ∑ d ∈ N.divisors, Nat.totient d := by
        unfold cuspCount
        refine Finset.sum_le_sum (fun d hd => ?_)
        exact Nat.le_of_dvd (Nat.totient_pos.mpr (Nat.pos_of_mem_divisors hd))
          (Nat.totient_dvd_of_dvd (Nat.gcd_dvd_left _ _))
    _ = N := Nat.sum_totient N

theorem nuTwo_le_dedekindPsi {N : ℕ} (hN : N ≠ 0) : nuTwo N ≤ dedekindPsi N :=
  (nuTwo_le_self hN).trans (le_dedekindPsi N hN)

theorem nuThree_le_dedekindPsi {N : ℕ} (hN : N ≠ 0) : nuThree N ≤ dedekindPsi N :=
  (nuThree_le_self hN).trans (le_dedekindPsi N hN)

theorem cuspCount_le_dedekindPsi {N : ℕ} (hN : N ≠ 0) : cuspCount N ≤ dedekindPsi N :=
  (cuspCount_le_self N).trans (le_dedekindPsi N hN)

end NuLeBounds
p2m_reactivate "P2MW.S_ModularCurve_genusFormula_isNat.ModularCurve"

section PrimePowGrowth

variable {p k : ℕ}

private theorem half_add_half_pred_PsiGrowt (hk : 0 < k) : k / 2 + (k - 1) / 2 = k - 1 := by omega

theorem dedekindPsi_sub_six_cuspCount_prime_pow (hp : p.Prime) (hk : 2 ≤ k)
    (hpk : 49 < p ^ k) :
    (15 : ℤ) ≤ (dedekindPsi (p ^ k) : ℤ) - 6 * (cuspCount (p ^ k) : ℤ) := by
  rw [dedekindPsi_prime_pow p k hp (by omega), cuspCount_prime_pow hp (by omega)]

  have hcd : p ^ (k / 2) * p ^ ((k - 1) / 2) = p ^ (k - 1) := by
    rw [← pow_add, half_add_half_pred_PsiGrowt (by omega)]
  have hpk' : p ^ k = p * p ^ (k - 1) := by
    conv_lhs => rw [show k = (k - 1) + 1 by omega, pow_succ, mul_comm]
  set c := p ^ (k / 2) with hc
  set d := p ^ ((k - 1) / 2) with hd
  have hcd' : (c : ℤ) * d = (p : ℤ) ^ (k - 1) := by exact_mod_cast hcd
  have hpkZ : (p : ℤ) ^ k = (p : ℤ) * ((c : ℤ) * d) := by
    rw [hcd']; exact_mod_cast hpk'

  have htarget : ((p ^ k + p ^ (k - 1) : ℕ) : ℤ) - 6 * ((c + d : ℕ) : ℤ)
      = (p : ℤ) * ((c : ℤ) * d) + (c : ℤ) * d - 6 * c - 6 * d := by
    push_cast; rw [← hcd', hpkZ]; ring
  rw [htarget]
  have hd1 : (1 : ℤ) ≤ (d : ℤ) := by
    have : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ hp.pos.ne')
    exact_mod_cast this

  rcases Nat.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
  ·
    have hced : c = p * d := by
      rw [hc, hd, ← pow_succ']; congr 1; omega
    have hcedZ : (c : ℤ) = p * d := by exact_mod_cast hced
    have hfac : (p : ℤ) * ((c : ℤ) * d) + (c : ℤ) * d - 6 * c - 6 * d
        = ((c : ℤ) - 6) * ((c : ℤ) + d) := by rw [hcedZ]; ring
    rw [hfac]

    have hcc : c * c = p ^ (2 * m) := by rw [hc, ← pow_add]; congr 1; omega
    have hc8 : (8 : ℤ) ≤ (c : ℤ) := by
      have hc7 : 7 < c := by nlinarith [hcc, hpk]
      exact_mod_cast hc7
    nlinarith [hd1, hc8]
  ·
    have hcd_eq : c = d := by rw [hc, hd]; congr 1; omega
    have hcdZ : (c : ℤ) = d := by exact_mod_cast hcd_eq
    have hfac : (p : ℤ) * ((c : ℤ) * d) + (c : ℤ) * d - 6 * c - 6 * d
        = ((p : ℤ) * d ^ 2 - 50) + ((d : ℤ) - 6) ^ 2 + 14 := by rw [hcdZ]; ring
    rw [hfac]

    have hpdd : p * d ^ 2 = p ^ (2 * m + 1) := by
      rw [hd, ← pow_mul, ← pow_succ']; congr 1; omega
    have hpd2 : (50 : ℤ) ≤ (p : ℤ) * (d : ℤ) ^ 2 := by
      have h50 : 50 ≤ p * d ^ 2 := hpdd ▸ hpk
      have : ((p * d ^ 2 : ℕ) : ℤ) = (p : ℤ) * (d : ℤ) ^ 2 := by push_cast; ring
      linarith [this ▸ (Int.ofNat_le.mpr h50 : (50 : ℤ) ≤ ((p * d ^ 2 : ℕ) : ℤ))]
    have hd6 : d ≠ 6 := by
      intro h6
      have h2 : (2 : ℕ) ∣ d := h6 ▸ ⟨3, rfl⟩
      have h3 : (3 : ℕ) ∣ d := h6 ▸ ⟨2, rfl⟩
      have hp2' : p = 2 := ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp
        (Nat.prime_two.dvd_of_dvd_pow (hd ▸ h2))).symm
      have hp3' : p = 3 := ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
        (Nat.prime_three.dvd_of_dvd_pow (hd ▸ h3))).symm
      omega
    have hd62 : (1 : ℤ) ≤ ((d : ℤ) - 6) ^ 2 := by
      have hdZ6 : (d : ℤ) ≠ 6 := fun h => hd6 (by exact_mod_cast h)
      rcases lt_or_gt_of_ne hdZ6 with h | h <;> nlinarith
    linarith

theorem psiGrowthBound_prime_pow_of_lt (hp : p.Prime) (hk : 2 ≤ k) (hpk : 49 < p ^ k) :
    PsiGrowthBound (p ^ k) := by
  have hpk0 : p ^ k ≠ 0 := pow_ne_zero _ hp.pos.ne'
  rw [psiGrowthBound_iff_lt_genusFormulaNum hpk0]
  unfold genusFormulaNum
  rw [dedekindPsiFin_eq, nuTwoFin_eq hpk0, nuThreeFin_eq hpk0]
  have h2 : (nuTwo (p ^ k) : ℤ) ≤ 2 := by
    exact_mod_cast nuTwo_prime_pow_le_two hp (by omega)
  have h3 : (nuThree (p ^ k) : ℤ) ≤ 2 := by
    exact_mod_cast nuThree_prime_pow_le_two hp (by omega)
  have hψ := dedekindPsi_sub_six_cuspCount_prime_pow hp hk hpk
  linarith

theorem psiGrowthBound_of_isPrimePow_of_lt {M : ℕ} (hM : IsPrimePow M) (hM49 : 49 < M) :
    PsiGrowthBound M := by
  obtain ⟨p, k, hp, hk, rfl⟩ := hM
  rcases Nat.lt_or_ge k 2 with hk1 | hk2
  · interval_cases k
    rw [pow_one] at hM49 ⊢
    exact psiGrowthBound_of_prime_of_lt hp.nat_prime (by omega)
  · exact psiGrowthBound_prime_pow_of_lt hp.nat_prime hk2 hM49

end PrimePowGrowth
p2m_reactivate "P2MW.S_ModularCurve_genusFormula_isNat.ModularCurve"

section CoprimeSplit

theorem genusFormulaNum_eq {N : ℕ} (hN : N ≠ 0) :
    genusFormulaNum N = 12 + (dedekindPsi N : ℤ) - 3 * (nuTwo N : ℤ)
      - 4 * (nuThree N : ℤ) - 6 * (cuspCount N : ℤ) := by
  unfold genusFormulaNum
  rw [dedekindPsiFin_eq, nuTwoFin_eq hN, nuThreeFin_eq hN]

theorem genusFormulaNum_mul_sub_twelve_ge {A B : ℕ} (hA : A ≠ 0) (hB : B ≠ 0)
    (hAB : Nat.Coprime A B) :
    (dedekindPsi B : ℤ) * (genusFormulaNum A - 12) ≤ genusFormulaNum (A * B) - 12 := by
  rw [genusFormulaNum_eq hA, genusFormulaNum_eq (mul_ne_zero hA hB),
    dedekindPsi_mul_of_coprime A B hAB, nuTwo_mul_of_coprime hAB,
    nuThree_mul_of_coprime hAB, cuspCount_mul_of_coprime hA hB hAB]
  push_cast
  have h2 : (nuTwo B : ℤ) ≤ dedekindPsi B := by exact_mod_cast nuTwo_le_dedekindPsi hB
  have h3 : (nuThree B : ℤ) ≤ dedekindPsi B := by exact_mod_cast nuThree_le_dedekindPsi hB
  have hc : (cuspCount B : ℤ) ≤ dedekindPsi B := by exact_mod_cast cuspCount_le_dedekindPsi hB
  have h2' : 0 ≤ (nuTwo A : ℤ) := Int.natCast_nonneg _
  have h3' : 0 ≤ (nuThree A : ℤ) := Int.natCast_nonneg _
  have hc' : 0 ≤ (cuspCount A : ℤ) := Int.natCast_nonneg _
  nlinarith [h2, h3, hc, h2', h3', hc']

theorem twelve_lt_genusFormulaNum_mul_of_left {A B : ℕ} (hA : A ≠ 0) (hB : B ≠ 0)
    (hAB : Nat.Coprime A B) (hgA : 12 < genusFormulaNum A) :
    12 < genusFormulaNum (A * B) := by
  have hψB : (1 : ℤ) ≤ (dedekindPsi B : ℤ) := by
    exact_mod_cast dedekindPsi_pos B hB
  have hkey := genusFormulaNum_mul_sub_twelve_ge hA hB hAB
  have : (1 : ℤ) ≤ (dedekindPsi B : ℤ) * (genusFormulaNum A - 12) := by
    calc (1 : ℤ) ≤ 1 * (genusFormulaNum A - 12) := by linarith
      _ ≤ (dedekindPsi B : ℤ) * (genusFormulaNum A - 12) := by
          apply mul_le_mul_of_nonneg_right hψB; linarith
  linarith

end CoprimeSplit
p2m_reactivate "P2MW.S_ModularCurve_genusFormula_isNat.ModularCurve"

section Residual

def genusFormulaNumProd (A B : ℕ) : ℤ :=
  12 + (dedekindPsiFin A * dedekindPsiFin B : ℤ)
    - 3 * (nuTwoFin A * nuTwoFin B : ℤ) - 4 * (nuThreeFin A * nuThreeFin B : ℤ)
    - 6 * (cuspCount A * cuspCount B : ℤ)

theorem genusFormulaNumProd_eq {A B : ℕ} (hA : A ≠ 0) (hB : B ≠ 0)
    (hAB : Nat.Coprime A B) : genusFormulaNumProd A B = genusFormulaNum (A * B) := by
  rw [genusFormulaNum_eq (mul_ne_zero hA hB), genusFormulaNumProd,
    dedekindPsi_mul_of_coprime A B hAB, nuTwo_mul_of_coprime hAB,
    nuThree_mul_of_coprime hAB, cuspCount_mul_of_coprime hA hB hAB,
    dedekindPsiFin_eq, dedekindPsiFin_eq, nuTwoFin_eq hA, nuTwoFin_eq hB,
    nuThreeFin_eq hA, nuThreeFin_eq hB]
  push_cast; ring

def genusLeOneLevels : List ℕ :=
  [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 24, 25, 27,
   32, 36, 49]

theorem mem_genusLeOneLevels_of_le {N : ℕ} (hN1 : 2 ≤ N) (hN49 : N ≤ 49)
    (hgN : genusFormulaNum N ≤ 12) : N ∈ genusLeOneLevels := by
  have hkernel : ∀ M ∈ Finset.Ico 2 50,
      genusFormulaNum M ≤ 12 → M ∈ genusLeOneLevels := by decide
  exact hkernel N (Finset.mem_Ico.mpr ⟨hN1, by omega⟩) hgN

theorem residualGrowthBound_decide :
    ∀ A ∈ genusLeOneLevels, ∀ B ∈ genusLeOneLevels,
      Nat.Coprime A B → 49 < A * B → 12 < genusFormulaNumProd A B := by
  decide

end Residual
p2m_reactivate "P2MW.S_ModularCurve_genusFormula_isNat.ModularCurve"

theorem psiGrowthBound_of_lt : ∀ M : ℕ, 49 < M → PsiGrowthBound M := by
  intro M
  induction M using Nat.strong_induction_on with
  | _ M ih =>
    intro hM49
    have hM0 : M ≠ 0 := by omega
    rw [psiGrowthBound_iff_lt_genusFormulaNum hM0]

    obtain ⟨p, hp, hpdvd⟩ := M.exists_prime_and_dvd (by omega)
    set a := M.factorization p with ha
    set A := p ^ a with hA
    set B := M / A with hB
    have ha1 : 1 ≤ a := by
      rw [ha]; exact (hp.dvd_iff_one_le_factorization hM0).mp hpdvd
    have hAdvd : A ∣ M := Nat.ordProj_dvd M p
    have hM_eq : M = A * B := (Nat.div_mul_cancel hAdvd).symm.trans (mul_comm _ _)
    have hA0 : A ≠ 0 := pow_ne_zero _ hp.pos.ne'
    have hB0 : B ≠ 0 := fun h => hM0 (by rw [hM_eq, h, mul_zero])
    have hAB : Nat.Coprime A B := (Nat.coprime_ordCompl hp hM0).pow_left a
    have hA_pp : IsPrimePow A := ⟨p, a, hp.prime, ha1, rfl⟩
    have hA2 : 2 ≤ A := hA_pp.one_lt

    rcases eq_or_ne B 1 with hB1 | hB1
    · have hMA : M = A := by rw [hM_eq, hB1, mul_one]
      rw [hMA]
      exact (psiGrowthBound_iff_lt_genusFormulaNum hA0).mp
        (psiGrowthBound_of_isPrimePow_of_lt hA_pp (hMA ▸ hM49))

    have hB2 : 2 ≤ B := (Nat.two_le_iff B).mpr ⟨hB0, hB1⟩
    have hBlt : B < M := by
      conv_rhs => rw [hM_eq]
      calc B = 1 * B := (one_mul B).symm
        _ < A * B := (Nat.mul_lt_mul_right (by omega)).mpr (by omega)

    by_cases hgA : 12 < genusFormulaNum A
    · rw [hM_eq]; exact twelve_lt_genusFormulaNum_mul_of_left hA0 hB0 hAB hgA

    by_cases hgB : 12 < genusFormulaNum B
    · rw [hM_eq, mul_comm]
      exact twelve_lt_genusFormulaNum_mul_of_left hB0 hA0 hAB.symm hgB

    have hgA' : genusFormulaNum A ≤ 12 := not_lt.mp hgA
    have hgB' : genusFormulaNum B ≤ 12 := not_lt.mp hgB
    have hA49 : A ≤ 49 := by
      by_contra h
      exact absurd ((psiGrowthBound_iff_lt_genusFormulaNum hA0).mp
        (psiGrowthBound_of_isPrimePow_of_lt hA_pp (not_le.mp h))) (not_lt.mpr hgA')
    have hB49 : B ≤ 49 := by
      by_contra h
      exact absurd ((psiGrowthBound_iff_lt_genusFormulaNum hB0).mp
        (ih B hBlt (not_le.mp h))) (not_lt.mpr hgB')
    have hAmem := mem_genusLeOneLevels_of_le hA2 hA49 hgA'
    have hBmem := mem_genusLeOneLevels_of_le hB2 hB49 hgB'
    rw [hM_eq, ← genusFormulaNumProd_eq hA0 hB0 hAB]
    exact residualGrowthBound_decide A hAmem B hBmem hAB (hM_eq ▸ hM49)

theorem genusFormula_eq_one_iff_mem_genusOneLevels' {M : ℕ} (hM : 0 < M) :
    genusFormula M = 1 ↔ M ∈ genusOneLevels :=
  genusFormula_eq_one_iff_mem_genusOneLevels hM (fun h49 => psiGrowthBound_of_lt M h49)

end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_genusFormula_isNat.ModularCurve"

set_option autoImplicit false

namespace ModularCurve
p2m_export "ModularCurve" "nuTwo nuThree cuspCount cuspCount_one genusFormula dedekindPsi dedekindPsi_one ModularPolynomialData ModularPolynomialData.natDegree_eq cuspCount_prime"
p2m_open "ModularCurve"

open Finset

theorem genusFormula_eq_zero_of_mem_genusZeroLevels {M : ℕ} (hM : M ∈ genusZeroLevels) :
    genusFormula M = 0 := by
  have hmem : genusFormula M ∈ genusZeroLevels.map genusFormula := List.mem_map_of_mem hM
  rw [genusFormula_genusZeroLevels] at hmem
  exact List.eq_of_mem_replicate hmem

theorem one_lt_genusFormula_of_notMem_of_notMem {M : ℕ} (hM : 0 < M)
    (h0 : M ∉ genusZeroLevels) (h1 : M ∉ genusOneLevels) : 1 < genusFormula M := by
  rcases le_or_gt M 49 with h49 | h49
  · have hnum := twelve_lt_genusFormulaNum_of_le_fortyNine_of_notMem M
      (Finset.mem_Ico.mpr ⟨hM, by omega⟩) h0 h1
    exact one_lt_genusFormula_of_psiGrowthBound
      ((psiGrowthBound_iff_lt_genusFormulaNum hM.ne').mpr hnum)
  · exact one_lt_genusFormula_of_psiGrowthBound (psiGrowthBound_of_lt M h49)

theorem genusFormula_nonneg {M : ℕ} (hM : 0 < M) : 0 ≤ genusFormula M := by
  by_cases h0 : M ∈ genusZeroLevels
  · rw [genusFormula_eq_zero_of_mem_genusZeroLevels h0]
  by_cases h1 : M ∈ genusOneLevels
  · rw [(genusFormula_eq_one_iff_mem_genusOneLevels' hM).mpr h1]; norm_num
  · linarith [one_lt_genusFormula_of_notMem_of_notMem hM h0 h1]

end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_genusFormula_isNat.ModularCurve"

set_option autoImplicit false

open CongruenceSubgroup

namespace ModularCurve
p2m_export "ModularCurve" "nuTwo nuThree cuspCount cuspCount_one genusFormula dedekindPsi dedekindPsi_one ModularPolynomialData ModularPolynomialData.natDegree_eq cuspCount_prime"
p2m_open "ModularCurve"

open CuspForm

def XZeroGenusFormulaIsNat (M : ℕ) : Prop :=
  ∃ d : ℕ, (d : ℚ) = genusFormula M

theorem xZeroGenusFormulaIsNat_of_twelve_dvd {M : ℕ} (hM : 0 < M)
    (hdvd : (12 : ℤ) ∣ genusFormulaNum M) : XZeroGenusFormulaIsNat M := by
  obtain ⟨k, hk⟩ := hdvd
  have hcast : genusFormula M = (k : ℚ) := by
    have h12 : (12 : ℚ) * genusFormula M = 12 * (k : ℚ) := by
      rw [← genusFormulaNum_cast hM.ne', hk]; push_cast; ring
    linarith
  have hknn : 0 ≤ k := by
    have hg := genusFormula_nonneg hM
    rw [hcast] at hg
    exact_mod_cast hg
  refine ⟨k.toNat, ?_⟩
  have hkc : ((k.toNat : ℤ) : ℚ) = (k : ℚ) := by
    exact_mod_cast congrArg ((↑·) : ℤ → ℚ) (Int.toNat_of_nonneg hknn)
  simp only [hcast, ← hkc, Int.cast_natCast]

end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_genusFormula_isNat.ModularCurve"

set_option autoImplicit false

open CongruenceSubgroup

namespace ModularCurve
p2m_export "ModularCurve" "nuTwo nuThree cuspCount cuspCount_one genusFormula dedekindPsi dedekindPsi_one ModularPolynomialData ModularPolynomialData.natDegree_eq cuspCount_prime"
p2m_open "ModularCurve"

open CuspForm

theorem genusFormulaNum_prime {p : ℕ} (hp : p.Prime) :
    genusFormulaNum p = (p : ℤ) + 1 - 3 * (nuTwo p : ℤ) - 4 * (nuThree p : ℤ) := by
  rw [genusFormulaNum_eq hp.pos.ne', dedekindPsi_prime hp, cuspCount_prime hp]
  push_cast; ring

private lemma three_dvd_aux_HIBGenus {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) :
    (3 : ℤ) ∣ (p : ℤ) + 1 - 4 * (nuThree p : ℤ) := by

  have h3nd : ¬(3 : ℕ) ∣ p :=
    fun h => hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h).symm
  have hq : p = 3 * (p / 3) + p % 3 := (Nat.div_add_mod p 3).symm
  have hmod := Nat.mod_lt p (show 0 < 3 by norm_num)
  have hmodne : p % 3 ≠ 0 := fun h => h3nd (Nat.dvd_of_mod_eq_zero h)
  by_cases h1 : p % 3 = 1
  · rw [nuThree_eq_two_of_mod_three_eq_one hp h1]
    refine ⟨p / 3 - 2, ?_⟩; push_cast; omega
  · have h2 : p % 3 = 2 := by omega
    rw [nuThree_eq_zero_of_mod_three_eq_two hp h2]
    refine ⟨p / 3 + 1, ?_⟩; push_cast; omega

private lemma four_dvd_aux_HIBGenus {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    (4 : ℤ) ∣ (p : ℤ) + 1 - 3 * (nuTwo p : ℤ) := by

  have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
  have hq : p = 4 * (p / 4) + p % 4 := (Nat.div_add_mod p 4).symm
  have hmod := Nat.mod_lt p (show 0 < 4 by norm_num)
  by_cases h1 : p % 4 = 1
  · rw [nuTwo_eq_two_of_mod_four_eq_one hp h1]
    refine ⟨p / 4 - 1, ?_⟩; push_cast; omega
  · have h3 : p % 4 = 3 := by omega
    rw [nuTwo_eq_zero_of_mod_four_eq_three hp h3]
    refine ⟨p / 4 + 1, ?_⟩; push_cast; omega

theorem twelve_dvd_genusFormulaNum_prime {p : ℕ} (hp : p.Prime) :
    (12 : ℤ) ∣ genusFormulaNum p := by
  rw [genusFormulaNum_prime hp]

  rcases eq_or_ne p 2 with rfl | hp2
  · rw [nuTwo_two, nuThree_two]; decide
  rcases eq_or_ne p 3 with rfl | hp3
  · rw [nuTwo_three, nuThree_three]; decide

  have h3 : (3 : ℤ) ∣ (p : ℤ) + 1 - 3 * (nuTwo p : ℤ) - 4 * (nuThree p : ℤ) := by
    have := three_dvd_aux_HIBGenus hp hp3
    omega
  have h4 : (4 : ℤ) ∣ (p : ℤ) + 1 - 3 * (nuTwo p : ℤ) - 4 * (nuThree p : ℤ) := by
    have := four_dvd_aux_HIBGenus hp hp2
    omega
  omega

private lemma nuThree_two_pow_HIBGenus {k : ℕ} (hk : 0 < k) : nuThree (2 ^ k) = 0 :=
  Nat.le_zero.mp <| nuThree_two ▸
    nuThree_prime_pow_le_nuThree_prime Nat.prime_two (by norm_num) hk

private lemma nuTwo_three_pow_HIBGenus {k : ℕ} (hk : 0 < k) : nuTwo (3 ^ k) = 0 :=
  Nat.le_zero.mp <| nuTwo_three ▸
    nuTwo_prime_pow_le_nuTwo_prime Nat.prime_three (by norm_num) hk

private lemma genusFormulaNum_two_pow_eq_HIBGenus {k : ℕ} (hk : 2 ≤ k) :
    genusFormulaNum (2 ^ k) = 12 + 3 * 2 ^ (k - 1)
      - 6 * ((2 : ℤ) ^ (k / 2) + 2 ^ ((k - 1) / 2)) := by
  have h4dvd : (4 : ℕ) ∣ 2 ^ k := by
    have : (2 : ℕ) ^ 2 ∣ 2 ^ k := pow_dvd_pow 2 hk; simpa using this
  rw [genusFormulaNum_eq (pow_ne_zero k two_ne_zero),
    dedekindPsi_prime_pow 2 k Nat.prime_two (by omega),
    nuTwo_eq_zero_of_four_dvd h4dvd, nuThree_two_pow_HIBGenus (by omega),
    cuspCount_prime_pow Nat.prime_two (show 0 < k by omega)]
  have hpk : (2 : ℕ) ^ k = 2 * 2 ^ (k - 1) := by
    conv_lhs => rw [show k = (k - 1) + 1 from (Nat.sub_add_cancel (by omega)).symm, pow_succ]
    ring
  push_cast [hpk]; ring

theorem twelve_dvd_genusFormulaNum_two_pow {k : ℕ} (hk : 0 < k) :
    (12 : ℤ) ∣ genusFormulaNum (2 ^ k) := by

  rcases Nat.lt_or_ge k 3 with hk1 | hk3
  · interval_cases k <;> decide

  rw [genusFormulaNum_two_pow_eq_HIBGenus (by omega)]

  have h3 : (3 : ℤ) ∣ 12 + 3 * 2 ^ (k - 1)
      - 6 * ((2 : ℤ) ^ (k / 2) + 2 ^ ((k - 1) / 2)) := by
    refine ⟨4 + 2 ^ (k - 1) - 2 * ((2 : ℤ) ^ (k / 2) + 2 ^ ((k - 1) / 2)), ?_⟩; ring

  have h4 : (4 : ℤ) ∣ 12 + 3 * 2 ^ (k - 1)
      - 6 * ((2 : ℤ) ^ (k / 2) + 2 ^ ((k - 1) / 2)) := by
    have h1 : (4 : ℤ) ∣ (2 : ℤ) ^ (k - 1) := by
      have := pow_dvd_pow (2 : ℤ) (show 2 ≤ k - 1 by omega); norm_num at this; exact this
    have h2 : (2 : ℤ) ∣ (2 : ℤ) ^ (k / 2) := dvd_pow_self 2 (by omega : k / 2 ≠ 0)
    have h2' : (2 : ℤ) ∣ (2 : ℤ) ^ ((k - 1) / 2) :=
      dvd_pow_self 2 (by omega : (k - 1) / 2 ≠ 0)
    obtain ⟨a, ha⟩ := h1; obtain ⟨b, hb⟩ := h2; obtain ⟨c, hc⟩ := h2'
    refine ⟨3 + 3 * a - 3 * (b + c), ?_⟩; rw [ha, hb, hc]; ring
  omega

private lemma genusFormulaNum_three_pow_eq_HIBGenus {k : ℕ} (hk : 2 ≤ k) :
    genusFormulaNum (3 ^ k) = 12 + 4 * 3 ^ (k - 1)
      - 6 * ((3 : ℤ) ^ (k / 2) + 3 ^ ((k - 1) / 2)) := by
  have h9dvd : (9 : ℕ) ∣ 3 ^ k := by
    have : (3 : ℕ) ^ 2 ∣ 3 ^ k := pow_dvd_pow 3 hk; simpa using this
  rw [genusFormulaNum_eq (pow_ne_zero k three_ne_zero),
    dedekindPsi_prime_pow 3 k Nat.prime_three (by omega),
    nuTwo_three_pow_HIBGenus (by omega), nuThree_eq_zero_of_nine_dvd h9dvd,
    cuspCount_prime_pow Nat.prime_three (show 0 < k by omega)]
  have hpk : (3 : ℕ) ^ k = 3 * 3 ^ (k - 1) := by
    conv_lhs => rw [show k = (k - 1) + 1 from (Nat.sub_add_cancel (by omega)).symm, pow_succ]
    ring
  push_cast [hpk]; ring

private lemma dvd_pow_sub_one_of_dvd_sub_one_HIBGenus {c a : ℤ} (ha : c ∣ a - 1) (n : ℕ) :
    c ∣ a ^ n - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨t, ht⟩ := ih; obtain ⟨s, hs⟩ := ha
    refine ⟨a * t + s, ?_⟩
    have hcalc : a ^ (n + 1) - 1 = a * (a ^ n - 1) + (a - 1) := by rw [pow_succ]; ring
    rw [hcalc, ht, hs]; ring

theorem twelve_dvd_genusFormulaNum_three_pow {k : ℕ} (hk : 0 < k) :
    (12 : ℤ) ∣ genusFormulaNum (3 ^ k) := by
  rcases Nat.lt_or_ge k 2 with hk1 | hk2
  · interval_cases k; decide
  rw [genusFormulaNum_three_pow_eq_HIBGenus hk2]

  have h3 : (3 : ℤ) ∣ 12 + 4 * 3 ^ (k - 1)
      - 6 * ((3 : ℤ) ^ (k / 2) + 3 ^ ((k - 1) / 2)) := by
    have h31 : (3 : ℤ) ∣ 4 * (3 : ℤ) ^ (k - 1) :=
      Dvd.dvd.mul_left (dvd_pow_self 3 (by omega : k - 1 ≠ 0)) _
    omega

  have h4 : (4 : ℤ) ∣ 12 + 4 * 3 ^ (k - 1)
      - 6 * ((3 : ℤ) ^ (k / 2) + 3 ^ ((k - 1) / 2)) := by
    have h3odd : (2 : ℤ) ∣ (3 : ℤ) - 1 := ⟨1, by ring⟩
    obtain ⟨c, hc⟩ := dvd_pow_sub_one_of_dvd_sub_one_HIBGenus h3odd (k / 2)
    obtain ⟨d, hd⟩ := dvd_pow_sub_one_of_dvd_sub_one_HIBGenus h3odd ((k - 1) / 2)
    refine ⟨3 + 3 ^ (k - 1) - 3 * (c + d + 1), ?_⟩; linarith
  omega

def NuTwoNuThreePrimePowEq : Prop :=
  (∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ k, 0 < k → nuTwo (p ^ k) = nuTwo p) ∧
  (∀ (p : ℕ), p.Prime → p ≠ 3 → ∀ k, 0 < k → nuThree (p ^ k) = nuThree p)

theorem genusFormulaNum_prime_pow_of_henselLift (h : NuTwoNuThreePrimePowEq)
    {p k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hk : 0 < k) :
    genusFormulaNum (p ^ k) = 12 + ((p : ℤ) ^ k + p ^ (k - 1))
      - 3 * (nuTwo p : ℤ) - 4 * (nuThree p : ℤ)
      - 6 * ((p : ℤ) ^ (k / 2) + p ^ ((k - 1) / 2)) := by
  rw [genusFormulaNum_eq (pow_ne_zero k hp.pos.ne'),
    dedekindPsi_prime_pow p k hp hk.ne', h.1 p hp hp2 k hk, h.2 p hp hp3 k hk,
    cuspCount_prime_pow hp hk]
  push_cast; ring

theorem twelve_dvd_genusFormulaNum_prime_pow_of_henselLift (h : NuTwoNuThreePrimePowEq)
    {p k : ℕ} (hp : p.Prime) (hk : 0 < k) :
    (12 : ℤ) ∣ genusFormulaNum (p ^ k) := by
  rcases eq_or_ne p 2 with rfl | hp2
  · exact twelve_dvd_genusFormulaNum_two_pow hk
  rcases eq_or_ne p 3 with rfl | hp3
  · exact twelve_dvd_genusFormulaNum_three_pow hk
  rw [genusFormulaNum_prime_pow_of_henselLift h hp hp2 hp3 hk]

  have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
  have h3nd : ¬(3 : ℕ) ∣ p :=
    fun hd => hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp hd).symm

  have hpk : (p : ℤ) ^ k = (p : ℤ) ^ (k - 1) * p := by
    conv_lhs => rw [show k = k - 1 + 1 from (Nat.sub_add_cancel hk).symm, pow_succ]
  have hkey : (12 : ℤ) + ((p : ℤ) ^ k + p ^ (k - 1)) - 3 * (nuTwo p : ℤ)
      - 4 * (nuThree p : ℤ) - 6 * ((p : ℤ) ^ (k / 2) + p ^ ((k - 1) / 2))
      = ((p : ℤ) + 1 - 3 * nuTwo p - 4 * nuThree p)
        + ((p : ℤ) ^ (k - 1) - 1) * (p + 1)
        - 6 * (((p : ℤ) ^ (k / 2) - 1) + (p ^ ((k - 1) / 2) - 1)) := by
    rw [hpk]; ring
  rw [hkey]
  have hprime12 := genusFormulaNum_prime hp ▸ twelve_dvd_genusFormulaNum_prime hp

  have hp_odd : (2 : ℤ) ∣ (p : ℤ) - 1 := by
    have hq : (p : ℤ) = 2 * ((p / 2 : ℕ) : ℤ) + 1 := by push_cast; omega
    exact ⟨(p / 2 : ℕ), by linarith⟩
  have h6term : (12 : ℤ) ∣ 6 * (((p : ℤ) ^ (k / 2) - 1) + (p ^ ((k - 1) / 2) - 1)) := by
    obtain ⟨a, ha⟩ := dvd_pow_sub_one_of_dvd_sub_one_HIBGenus hp_odd (k / 2)
    obtain ⟨b, hb⟩ := dvd_pow_sub_one_of_dvd_sub_one_HIBGenus hp_odd ((k - 1) / 2)
    exact ⟨a + b, by linarith⟩
  have hmidterm : (12 : ℤ) ∣ ((p : ℤ) ^ (k - 1) - 1) * (p + 1) := by

    obtain ⟨a, ha⟩ := dvd_pow_sub_one_of_dvd_sub_one_HIBGenus hp_odd (k - 1)
    obtain ⟨s, hs⟩ := hp_odd
    have hb : (p : ℤ) + 1 = 2 * (s + 1) := by linarith
    have h4 : (4 : ℤ) ∣ ((p : ℤ) ^ (k - 1) - 1) * (p + 1) :=
      ⟨a * (s + 1), by rw [ha, hb]; ring⟩

    have hq : p = 3 * (p / 3) + p % 3 := (Nat.div_add_mod p 3).symm
    have hpmod3 := Nat.mod_lt p (show 0 < 3 by norm_num)
    have hpmod3ne : p % 3 ≠ 0 := fun hh => h3nd (Nat.dvd_of_mod_eq_zero hh)
    have h3 : (3 : ℤ) ∣ ((p : ℤ) ^ (k - 1) - 1) * (p + 1) := by
      by_cases h1 : p % 3 = 1
      ·
        have h3dvd : (3 : ℤ) ∣ (p : ℤ) - 1 := by
          have hpq : (p : ℤ) = 3 * (p / 3 : ℕ) + 1 := by push_cast; omega
          exact ⟨p / 3, by linarith⟩
        exact Dvd.dvd.mul_right (dvd_pow_sub_one_of_dvd_sub_one_HIBGenus h3dvd (k - 1)) _
      ·
        have h2 : p % 3 = 2 := by omega
        have h3dvd : (3 : ℤ) ∣ (p : ℤ) + 1 := by
          have hpq : (p : ℤ) = 3 * ((p / 3 : ℕ) : ℤ) + 2 := by push_cast; omega
          exact ⟨((p / 3 : ℕ) : ℤ) + 1, by linarith⟩
        exact Dvd.dvd.mul_left h3dvd _

    obtain ⟨u, hu⟩ := h4; obtain ⟨v, hv⟩ := h3
    omega

  obtain ⟨a, ha⟩ := hprime12
  obtain ⟨b, hb⟩ := hmidterm
  obtain ⟨c, hc⟩ := h6term
  exact ⟨a + b - c, by linarith⟩

theorem three_dvd_genusFormulaNum_iff {M : ℕ} (hM : M ≠ 0) :
    (3 : ℤ) ∣ genusFormulaNum M ↔ (3 : ℤ) ∣ (dedekindPsi M : ℤ) - (nuThree M : ℤ) := by
  rw [genusFormulaNum_eq hM]; omega

theorem three_dvd_genusFormulaNum_mul_of_coprime {A B : ℕ} (hA : A ≠ 0) (hB : B ≠ 0)
    (hAB : Nat.Coprime A B) (h3A : (3 : ℤ) ∣ genusFormulaNum A)
    (h3B : (3 : ℤ) ∣ genusFormulaNum B) :
    (3 : ℤ) ∣ genusFormulaNum (A * B) := by
  rw [three_dvd_genusFormulaNum_iff (mul_ne_zero hA hB),
    dedekindPsi_mul_of_coprime A B hAB, nuThree_mul_of_coprime hAB]
  rw [three_dvd_genusFormulaNum_iff hA] at h3A
  rw [three_dvd_genusFormulaNum_iff hB] at h3B
  obtain ⟨a, ha⟩ := h3A
  obtain ⟨b, hb⟩ := h3B
  refine ⟨a * dedekindPsi B + nuThree A * b, ?_⟩
  have hcalc : (dedekindPsi A : ℤ) * dedekindPsi B - (nuThree A : ℤ) * nuThree B
      = ((dedekindPsi A : ℤ) - nuThree A) * dedekindPsi B
        + (nuThree A : ℤ) * ((dedekindPsi B : ℤ) - nuThree B) := by ring
  push_cast [hcalc, ha, hb]; ring

end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_genusFormula_isNat.ModularCurve"

set_option autoImplicit false

namespace ModularCurve
p2m_export "ModularCurve" "nuTwo nuThree cuspCount cuspCount_one genusFormula dedekindPsi dedekindPsi_one ModularPolynomialData ModularPolynomialData.natDegree_eq cuspCount_prime"
p2m_open "ModularCurve"

section HenselStep

variable {p k : ℕ}

private theorem pk_sq_eq_zero_HIBHense (hk : 0 < k) :
    ((p ^ k : ℕ) : ZMod (p ^ (k + 1))) * ((p ^ k : ℕ) : ZMod (p ^ (k + 1))) = 0 := by
  rw [← Nat.cast_mul, ← pow_add]
  exact (ZMod.natCast_eq_zero_iff _ _).mpr (pow_dvd_pow p (by omega))

private theorem pk_mul_eq_zero_iff_HIBHense (hp : p.Prime) (z : ZMod (p ^ (k + 1))) :
    ((p ^ k : ℕ) : ZMod (p ^ (k + 1))) * z = 0 ↔
      ZMod.castHom (dvd_pow_self p (Nat.succ_ne_zero k)) (ZMod p) z = 0 := by
  haveI : NeZero (p ^ (k + 1)) := ⟨pow_ne_zero _ hp.pos.ne'⟩
  conv_lhs => rw [← ZMod.natCast_zmod_val z, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
  rw [ZMod.castHom_apply, ← ZMod.natCast_val, ZMod.natCast_eq_zero_iff]
  constructor
  · rintro ⟨t, ht⟩
    rcases Nat.eq_zero_or_pos z.val with hv | hv
    · exact hv ▸ dvd_zero p
    · refine ⟨t, Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos k) ?_⟩
      rw [ht, pow_succ]; ring
  · rintro ⟨t, ht⟩; exact ⟨t, by rw [ht, pow_succ]; ring⟩

private theorem castHom_natCast_val_HIBHense (hp : p.Prime) (hk : 0 < k) (x : ZMod (p ^ k)) :
    ZMod.castHom (dvd_pow_self p (Nat.succ_ne_zero k)) (ZMod p)
        ((x.val : ℕ) : ZMod (p ^ (k + 1)))
      = ZMod.castHom (dvd_pow_self p hk.ne') (ZMod p) x := by
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.pos.ne'⟩
  rw [map_natCast, ZMod.castHom_apply, ZMod.natCast_val]

private theorem castHom_k_natCast_val_HIBHense (hp : p.Prime) (x : ZMod (p ^ k)) :
    ZMod.castHom (pow_dvd_pow p (Nat.le_succ k)) (ZMod (p ^ k))
        ((x.val : ℕ) : ZMod (p ^ (k + 1))) = x := by
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.pos.ne'⟩
  rw [map_natCast, ZMod.natCast_zmod_val]

private theorem exists_pk_mul_of_castHom_eq_zero_HIBHense (hp : p.Prime)
    {w : ZMod (p ^ (k + 1))}
    (hw : ZMod.castHom (pow_dvd_pow p (Nat.le_succ k)) (ZMod (p ^ k)) w = 0) :
    ∃ δ : ZMod (p ^ (k + 1)), w = ((p ^ k : ℕ) : ZMod (p ^ (k + 1))) * δ := by
  haveI : NeZero (p ^ (k + 1)) := ⟨pow_ne_zero _ hp.pos.ne'⟩
  rw [ZMod.castHom_apply, ← ZMod.natCast_val, ZMod.natCast_eq_zero_iff] at hw
  obtain ⟨d, hd⟩ := hw
  exact ⟨(d : ZMod (p ^ (k + 1))),
    by rw [← ZMod.natCast_zmod_val w, hd, Nat.cast_mul]⟩

theorem exists_lift_sq_add_one (hp : p.Prime) (hp2 : p ≠ 2) (hk : 0 < k)
    {x : ZMod (p ^ k)} (hx : x ^ 2 + 1 = 0) :
    ∃ ξ : ZMod (p ^ (k + 1)), ξ ^ 2 + 1 = 0 ∧
      ZMod.castHom (pow_dvd_pow p (Nat.le_succ k)) (ZMod (p ^ k)) ξ = x := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.pos.ne'⟩
  haveI : NeZero (p ^ (k + 1)) := ⟨pow_ne_zero _ hp.pos.ne'⟩

  set ξ₀ : ZMod (p ^ (k + 1)) := ((x.val : ℕ) : ZMod (p ^ (k + 1))) with hξ₀
  have hred : ZMod.castHom (pow_dvd_pow p (Nat.le_succ k)) (ZMod (p ^ k)) ξ₀ = x :=
    castHom_k_natCast_val_HIBHense hp x
  have hdefect : ZMod.castHom (pow_dvd_pow p (Nat.le_succ k)) (ZMod (p ^ k))
      (ξ₀ ^ 2 + 1) = 0 := by
    rw [map_add, map_pow, map_one, hred, hx]
  obtain ⟨δ, hδ⟩ := exists_pk_mul_of_castHom_eq_zero_HIBHense hp hdefect

  set s : ZMod p := ZMod.castHom (dvd_pow_self p hk.ne') (ZMod p) x with hs
  have hredP : ZMod.castHom (dvd_pow_self p (Nat.succ_ne_zero k)) (ZMod p) ξ₀ = s := by
    rw [hξ₀, castHom_natCast_val_HIBHense hp hk]
  have hs2 : s ^ 2 + 1 = 0 := by
    have := congrArg (ZMod.castHom (dvd_pow_self p hk.ne') (ZMod p)) hx
    simpa only [map_add, map_pow, map_one, map_zero] using this

  have h2s_unit : IsUnit (2 * s) := by
    have h2u : (2 : ZMod p) ≠ 0 := by
      have : ((2 : ℕ) : ZMod p) ≠ 0 := fun h =>
        hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
          ((ZMod.natCast_eq_zero_iff 2 p).mp h))
      exact_mod_cast this
    exact (Ne.isUnit h2u).mul (Ne.isUnit (ne_zero_of_sq_add_one_eq_zero hp hs2))

  set δ' : ZMod p := ZMod.castHom (dvd_pow_self p (Nat.succ_ne_zero k)) (ZMod p) δ
  set c' : ZMod p := -δ' * (2 * s)⁻¹ with hc'
  set c : ZMod (p ^ (k + 1)) := ((c'.val : ℕ) : ZMod (p ^ (k + 1))) with hc
  have hredPc : ZMod.castHom (dvd_pow_self p (Nat.succ_ne_zero k)) (ZMod p) c = c' := by
    rw [hc, map_natCast, ZMod.natCast_zmod_val]

  set pk : ZMod (p ^ (k + 1)) := ((p ^ k : ℕ) : ZMod (p ^ (k + 1)))
  refine ⟨ξ₀ + pk * c, ?_, ?_⟩
  ·

    have hpk2 : pk * pk = 0 := pk_sq_eq_zero_HIBHense hk
    have hexpand : (ξ₀ + pk * c) ^ 2 + 1 = pk * (δ + 2 * ξ₀ * c) := by
      have : (ξ₀ + pk * c) ^ 2 + 1
          = (ξ₀ ^ 2 + 1) + 2 * ξ₀ * (pk * c) + pk * pk * c ^ 2 := by ring
      rw [this, hδ, hpk2]; ring
    rw [hexpand, pk_mul_eq_zero_iff_HIBHense hp]
    rw [map_add, map_mul, map_mul, hredPc, hredP, map_ofNat, hc']
    have hinv : (2 * s) * (2 * s)⁻¹ = 1 := mul_inv_cancel₀ h2s_unit.ne_zero
    linear_combination (-δ') * hinv
  ·
    have hpkred : ZMod.castHom (pow_dvd_pow p (Nat.le_succ k)) (ZMod (p ^ k)) pk = 0 := by
      rw [map_natCast, ZMod.natCast_self]
    rw [map_add, map_mul, hpkred, zero_mul, add_zero, hred]

private theorem two_mul_add_one_ne_zero_of_root_HIBHense (hp : p.Prime) (hp3 : p ≠ 3)
    {ζ : ZMod p} (hζ : ζ ^ 2 + ζ + 1 = 0) : 2 * ζ + 1 ≠ 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro hcontra
  have h3 : (3 : ZMod p) = 0 := by
    linear_combination 4 * hζ - (2 * ζ + 1) * hcontra
  have hcast : ((3 : ℕ) : ZMod p) = 0 := by exact_mod_cast h3
  exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp
    ((ZMod.natCast_eq_zero_iff 3 p).mp hcast))

theorem exists_lift_sq_add_self_add_one (hp : p.Prime) (hp3 : p ≠ 3) (hk : 0 < k)
    {x : ZMod (p ^ k)} (hx : x ^ 2 + x + 1 = 0) :
    ∃ ξ : ZMod (p ^ (k + 1)), ξ ^ 2 + ξ + 1 = 0 ∧
      ZMod.castHom (pow_dvd_pow p (Nat.le_succ k)) (ZMod (p ^ k)) ξ = x := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.pos.ne'⟩
  haveI : NeZero (p ^ (k + 1)) := ⟨pow_ne_zero _ hp.pos.ne'⟩
  set ξ₀ : ZMod (p ^ (k + 1)) := ((x.val : ℕ) : ZMod (p ^ (k + 1))) with hξ₀
  have hred : ZMod.castHom (pow_dvd_pow p (Nat.le_succ k)) (ZMod (p ^ k)) ξ₀ = x :=
    castHom_k_natCast_val_HIBHense hp x
  have hdefect : ZMod.castHom (pow_dvd_pow p (Nat.le_succ k)) (ZMod (p ^ k))
      (ξ₀ ^ 2 + ξ₀ + 1) = 0 := by
    rw [map_add, map_add, map_pow, map_one, hred, hx]
  obtain ⟨δ, hδ⟩ := exists_pk_mul_of_castHom_eq_zero_HIBHense hp hdefect
  set s : ZMod p := ZMod.castHom (dvd_pow_self p hk.ne') (ZMod p) x with hs
  have hredP : ZMod.castHom (dvd_pow_self p (Nat.succ_ne_zero k)) (ZMod p) ξ₀ = s := by
    rw [hξ₀, castHom_natCast_val_HIBHense hp hk]
  have hs2 : s ^ 2 + s + 1 = 0 := by
    have := congrArg (ZMod.castHom (dvd_pow_self p hk.ne') (ZMod p)) hx
    simpa only [map_add, map_pow, map_one, map_zero] using this

  have hd_unit : IsUnit (2 * s + 1) :=
    Ne.isUnit (two_mul_add_one_ne_zero_of_root_HIBHense hp hp3 hs2)
  set δ' : ZMod p := ZMod.castHom (dvd_pow_self p (Nat.succ_ne_zero k)) (ZMod p) δ
  set c' : ZMod p := -δ' * (2 * s + 1)⁻¹ with hc'
  set c : ZMod (p ^ (k + 1)) := ((c'.val : ℕ) : ZMod (p ^ (k + 1))) with hc
  have hredPc : ZMod.castHom (dvd_pow_self p (Nat.succ_ne_zero k)) (ZMod p) c = c' := by
    rw [hc, map_natCast, ZMod.natCast_zmod_val]
  set pk : ZMod (p ^ (k + 1)) := ((p ^ k : ℕ) : ZMod (p ^ (k + 1)))
  refine ⟨ξ₀ + pk * c, ?_, ?_⟩
  · have hpk2 : pk * pk = 0 := pk_sq_eq_zero_HIBHense hk
    have hexpand : (ξ₀ + pk * c) ^ 2 + (ξ₀ + pk * c) + 1
        = pk * (δ + (2 * ξ₀ + 1) * c) := by
      have : (ξ₀ + pk * c) ^ 2 + (ξ₀ + pk * c) + 1
          = (ξ₀ ^ 2 + ξ₀ + 1) + (2 * ξ₀ + 1) * (pk * c) + pk * pk * c ^ 2 := by ring
      rw [this, hδ, hpk2]; ring
    rw [hexpand, pk_mul_eq_zero_iff_HIBHense hp]
    rw [map_add, map_mul, map_add, map_mul, map_one, hredPc, hredP, map_ofNat, hc']
    have hinv : (2 * s + 1) * (2 * s + 1)⁻¹ = 1 := mul_inv_cancel₀ hd_unit.ne_zero
    linear_combination (-δ') * hinv
  · have hpkred : ZMod.castHom (pow_dvd_pow p (Nat.le_succ k)) (ZMod (p ^ k)) pk = 0 := by
      rw [map_natCast, ZMod.natCast_self]
    rw [map_add, map_mul, hpkred, zero_mul, add_zero, hred]

end HenselStep
p2m_reactivate "P2MW.S_ModularCurve_genusFormula_isNat.ModularCurve"

section Surjective

variable {p k : ℕ}

theorem nuTwo_prime_pow_le_succ (hp : p.Prime) (hp2 : p ≠ 2) (hk : 0 < k) :
    nuTwo (p ^ k) ≤ nuTwo (p ^ (k + 1)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.pos.ne'⟩
  haveI : NeZero (p ^ (k + 1)) := ⟨pow_ne_zero _ hp.pos.ne'⟩
  unfold nuTwo
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  refine Fintype.card_le_of_surjective
    (fun z => ⟨ZMod.castHom (pow_dvd_pow p (Nat.le_succ k)) (ZMod (p ^ k)) z.1, ?_⟩) ?_
  · obtain ⟨x, hx⟩ := z
    have := congrArg (ZMod.castHom (pow_dvd_pow p (Nat.le_succ k)) (ZMod (p ^ k))) hx
    simpa only [map_add, map_pow, map_one, map_zero] using this
  · rintro ⟨x, hx⟩
    obtain ⟨ξ, hξ, hξred⟩ := exists_lift_sq_add_one hp hp2 hk hx
    exact ⟨⟨ξ, hξ⟩, Subtype.ext hξred⟩

theorem nuThree_prime_pow_le_succ (hp : p.Prime) (hp3 : p ≠ 3) (hk : 0 < k) :
    nuThree (p ^ k) ≤ nuThree (p ^ (k + 1)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.pos.ne'⟩
  haveI : NeZero (p ^ (k + 1)) := ⟨pow_ne_zero _ hp.pos.ne'⟩
  unfold nuThree
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  refine Fintype.card_le_of_surjective
    (fun z => ⟨ZMod.castHom (pow_dvd_pow p (Nat.le_succ k)) (ZMod (p ^ k)) z.1, ?_⟩) ?_
  · obtain ⟨x, hx⟩ := z
    have := congrArg (ZMod.castHom (pow_dvd_pow p (Nat.le_succ k)) (ZMod (p ^ k))) hx
    simpa only [map_add, map_pow, map_one, map_zero] using this
  · rintro ⟨x, hx⟩
    obtain ⟨ξ, hξ, hξred⟩ := exists_lift_sq_add_self_add_one hp hp3 hk hx
    exact ⟨⟨ξ, hξ⟩, Subtype.ext hξred⟩

theorem nuTwo_prime_le_nuTwo_prime_pow (hp : p.Prime) (hp2 : p ≠ 2) (hk : 0 < k) :
    nuTwo p ≤ nuTwo (p ^ k) := by
  induction k with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [pow_one]
    · exact (ih hn).trans (nuTwo_prime_pow_le_succ hp hp2 hn)

theorem nuThree_prime_le_nuThree_prime_pow (hp : p.Prime) (hp3 : p ≠ 3) (hk : 0 < k) :
    nuThree p ≤ nuThree (p ^ k) := by
  induction k with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [pow_one]
    · exact (ih hn).trans (nuThree_prime_pow_le_succ hp hp3 hn)

end Surjective
p2m_reactivate "P2MW.S_ModularCurve_genusFormula_isNat.ModularCurve"

theorem nuTwo_prime_pow_eq {p k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hk : 0 < k) :
    nuTwo (p ^ k) = nuTwo p :=
  le_antisymm (nuTwo_prime_pow_le_nuTwo_prime hp hp2 hk)
    (nuTwo_prime_le_nuTwo_prime_pow hp hp2 hk)

theorem nuThree_prime_pow_eq {p k : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) (hk : 0 < k) :
    nuThree (p ^ k) = nuThree p :=
  le_antisymm (nuThree_prime_pow_le_nuThree_prime hp hp3 hk)
    (nuThree_prime_le_nuThree_prime_pow hp hp3 hk)

theorem nuTwoNuThreePrimePowEq : NuTwoNuThreePrimePowEq :=
  ⟨fun _ hp hp2 _ hk => nuTwo_prime_pow_eq hp hp2 hk,
    fun _ hp hp3 _ hk => nuThree_prime_pow_eq hp hp3 hk⟩

theorem twelve_dvd_genusFormulaNum_prime_pow {p k : ℕ} (hp : p.Prime) (hk : 0 < k) :
    (12 : ℤ) ∣ genusFormulaNum (p ^ k) :=
  twelve_dvd_genusFormulaNum_prime_pow_of_henselLift nuTwoNuThreePrimePowEq hp hk

end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_genusFormula_isNat.ModularCurve"

set_option autoImplicit false

namespace ModularCurve
p2m_export "ModularCurve" "nuTwo nuThree cuspCount cuspCount_one genusFormula dedekindPsi dedekindPsi_one ModularPolynomialData ModularPolynomialData.natDegree_eq cuspCount_prime"
p2m_open "ModularCurve"

section Parity

theorem two_dvd_nuTwo_prime_pow_of_odd {p k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hk : 0 < k) : 2 ∣ nuTwo (p ^ k) := by
  rw [nuTwo_prime_pow_eq hp hp2 hk, nuTwo_prime hp hp2]
  split_ifs <;> omega

theorem two_dvd_cuspCount_prime_pow_of_odd {p k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hk : 0 < k) : 2 ∣ cuspCount (p ^ k) := by
  rw [cuspCount_prime_pow hp hk]
  have hodd : Odd p := hp.odd_of_ne_two hp2
  obtain ⟨a, ha⟩ : Odd (p ^ (k / 2)) := hodd.pow
  obtain ⟨b, hb⟩ : Odd (p ^ ((k - 1) / 2)) := hodd.pow
  omega

private lemma odd_prime_pow_ne_two_HIBHense {p n : ℕ} (hn : 0 < n)
    (hodd : Odd (p ^ n)) : p ≠ 2 := by
  rintro rfl
  obtain ⟨c, hc⟩ : (2 : ℕ) ∣ 2 ^ n := dvd_pow_self 2 hn.ne'
  obtain ⟨m, hm⟩ := hodd
  omega

theorem two_dvd_nuTwo_of_odd {M : ℕ} (hM : 1 < M) (hodd : Odd M) :
    2 ∣ nuTwo M := by
  induction M using Nat.recOnPosPrimePosCoprime with
  | prime_pow p n hp hn =>
      exact two_dvd_nuTwo_prime_pow_of_odd hp (odd_prime_pow_ne_two_HIBHense hn hodd) hn
  | zero => omega
  | one => omega
  | coprime a b ha _ hab iha _ =>
      have haodd : Odd a := (Nat.odd_mul.mp hodd).1
      rw [nuTwo_mul_of_coprime hab]
      exact Dvd.dvd.mul_right (iha ha haodd) _

theorem two_dvd_cuspCount_of_odd {M : ℕ} (hM : 1 < M) (hodd : Odd M) :
    2 ∣ cuspCount M := by
  induction M using Nat.recOnPosPrimePosCoprime with
  | prime_pow p n hp hn =>
      exact two_dvd_cuspCount_prime_pow_of_odd hp (odd_prime_pow_ne_two_HIBHense hn hodd) hn
  | zero => omega
  | one => omega
  | coprime a b ha hb hab iha _ =>
      have haodd : Odd a := (Nat.odd_mul.mp hodd).1
      rw [cuspCount_mul_of_coprime (by omega) (by omega) hab]
      exact Dvd.dvd.mul_right (iha ha haodd) _

theorem two_dvd_nuTwo_add_cuspCount_of_odd {M : ℕ} (hM : M ≠ 0) (hodd : Odd M) :
    (2 : ℤ) ∣ (nuTwo M : ℤ) + (cuspCount M : ℤ) := by
  rcases Nat.lt_or_ge 1 M with h1 | h1
  · have h2 := two_dvd_nuTwo_of_odd h1 hodd
    have hc := two_dvd_cuspCount_of_odd h1 hodd
    omega
  · obtain rfl : M = 1 := by omega
    rw [nuTwo_one, cuspCount_one]; decide

theorem two_dvd_nuTwo_add_cuspCount_mul_of_coprime {A B : ℕ} (hA : A ≠ 0) (hB : B ≠ 0)
    (hAB : Nat.Coprime A B) :
    (2 : ℤ) ∣ ((nuTwo A : ℤ) + cuspCount A) * ((nuTwo B : ℤ) + cuspCount B) := by
  rcases Nat.even_or_odd A with hAev | hAodd
  ·
    have hBodd : Odd B := by
      rcases Nat.even_or_odd B with hBev | hBodd
      · have h21 : (2 : ℕ) ∣ 1 := hAB ▸ Nat.dvd_gcd hAev.two_dvd hBev.two_dvd
        omega
      · exact hBodd
    exact Dvd.dvd.mul_left (two_dvd_nuTwo_add_cuspCount_of_odd hB hBodd) _
  · exact Dvd.dvd.mul_right (two_dvd_nuTwo_add_cuspCount_of_odd hA hAodd) _

end Parity
p2m_reactivate "P2MW.S_ModularCurve_genusFormula_isNat.ModularCurve"

theorem four_dvd_genusFormulaNum_iff {M : ℕ} (hM : M ≠ 0) :
    (4 : ℤ) ∣ genusFormulaNum M ↔
      (4 : ℤ) ∣ (dedekindPsi M : ℤ) - 3 * (nuTwo M : ℤ) - 6 * (cuspCount M : ℤ) := by
  rw [genusFormulaNum_eq hM]; omega

theorem four_dvd_genusFormulaNum_mul_of_coprime {A B : ℕ} (hA : A ≠ 0) (hB : B ≠ 0)
    (hAB : Nat.Coprime A B) (h4A : (4 : ℤ) ∣ genusFormulaNum A)
    (h4B : (4 : ℤ) ∣ genusFormulaNum B) :
    (4 : ℤ) ∣ genusFormulaNum (A * B) := by
  rw [four_dvd_genusFormulaNum_iff (mul_ne_zero hA hB),
    dedekindPsi_mul_of_coprime A B hAB, nuTwo_mul_of_coprime hAB,
    cuspCount_mul_of_coprime hA hB hAB]
  push_cast
  rw [four_dvd_genusFormulaNum_iff hA] at h4A
  rw [four_dvd_genusFormulaNum_iff hB] at h4B
  obtain ⟨s, hs⟩ := h4A
  obtain ⟨t, ht⟩ := h4B
  obtain ⟨u, hu⟩ := two_dvd_nuTwo_add_cuspCount_mul_of_coprime hA hB hAB
  refine ⟨4 * s * t + 3 * s * ((nuTwo B : ℤ) + 2 * cuspCount B)
      + 3 * t * ((nuTwo A : ℤ) + 2 * cuspCount A)
      + 3 * u
      + 3 * ((nuTwo A : ℤ) * cuspCount B + cuspCount A * nuTwo B
             + 2 * cuspCount A * cuspCount B), ?_⟩
  linear_combination (dedekindPsi B : ℤ) * hs
    + (3 * (nuTwo A : ℤ) + 6 * (cuspCount A : ℤ) + 4 * s) * ht + 6 * hu

theorem twelve_dvd_genusFormulaNum_mul_of_coprime {A B : ℕ} (hA : A ≠ 0) (hB : B ≠ 0)
    (hAB : Nat.Coprime A B) (h12A : (12 : ℤ) ∣ genusFormulaNum A)
    (h12B : (12 : ℤ) ∣ genusFormulaNum B) :
    (12 : ℤ) ∣ genusFormulaNum (A * B) := by
  have h3 := three_dvd_genusFormulaNum_mul_of_coprime hA hB hAB
    (dvd_trans (by norm_num) h12A) (dvd_trans (by norm_num) h12B)
  have h4 := four_dvd_genusFormulaNum_mul_of_coprime hA hB hAB
    (dvd_trans (by norm_num) h12A) (dvd_trans (by norm_num) h12B)
  omega

theorem twelve_dvd_genusFormulaNum {N : ℕ} (hN : N ≠ 0) :
    (12 : ℤ) ∣ genusFormulaNum N := by
  induction N using Nat.recOnPosPrimePosCoprime with
  | prime_pow p n hp hn => exact twelve_dvd_genusFormulaNum_prime_pow hp hn
  | zero => exact absurd rfl hN
  | one => decide
  | coprime a b ha hb hab iha ihb =>
      exact twelve_dvd_genusFormulaNum_mul_of_coprime (by omega) (by omega) hab
        (iha (by omega)) (ihb (by omega))

theorem xZeroGenusFormulaIsNat {N : ℕ} (hN : 0 < N) : XZeroGenusFormulaIsNat N :=
  xZeroGenusFormulaIsNat_of_twelve_dvd hN (twelve_dvd_genusFormulaNum hN.ne')

end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_genusFormula_isNat.ModularCurve"

theorem solution {N : ℕ} (hN : 0 < N) : ∃ g : ℕ, (g : ℚ) = ModularCurve.genusFormula N :=
  ModularCurve.xZeroGenusFormulaIsNat hN

end S_ModularCurve_genusFormula_isNat
end P2MW
export P2MW.S_ModularCurve_genusFormula_isNat (solution)
