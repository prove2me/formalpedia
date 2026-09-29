-- Prove2me | solution 1 for Ihara.ihxw14_dio_lemma22_statement_unconditional
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/592c6c81-5beb-5ed7-9f53-ddb45739f81a

import Theorems.Thm_Ihara_mennickeZ_eq_top_of_corrected_reading_of_diophantine
import Definitions.Def_IharaMennickeCarrier
import Mathlib.NumberTheory.Multiplicity
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Prime
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.Data.Nat.Totient
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Ihara_ihxw14_dio_lemma22_statement_unconditional

set_option Elab.async false
set_option autoImplicit false

namespace Ihara
p2m_export "Ihara" "mennickeZ_eq_top_of_corrected_reading_of_diophantine mennickeZ"
p2m_open "Ihara"

open Subgroup Matrix

open scoped MatrixGroups

open scoped commutatorElement

noncomputable section

section GenericDictionaries

variable {G : Type*} [Group G]

end GenericDictionaries

section EntryHelpers

variable (q : ℕ) [NeZero q]

end EntryHelpers

section TwoFifteen

variable (q : ℕ) [NeZero q]

end TwoFifteen

section WordIdentity

variable (q : ℕ) [NeZero q]

end WordIdentity

section TwoTwentyFour

variable (q m : ℕ) [NeZero q]

end TwoTwentyFour

section TwoTwenty

variable (q m : ℕ) [NeZero q]

end TwoTwenty

section TwoTwentySix

variable (q m : ℕ) [NeZero q]

end TwoTwentySix

section DirichletSteps

theorem dirichlet_exists_odd_prime_modEq_pair (n₁ n₂ : ℕ) (hn₁ : n₁ ≠ 0) (hn₂ : n₂ ≠ 0)
    (hcop : n₁.Coprime n₂) (a₁ a₂ : ℕ) (ha₁ : a₁.Coprime n₁) (ha₂ : a₂.Coprime n₂)
    (N : ℕ) :
    ∃ p : ℕ, N < p ∧ p.Prime ∧ Odd p ∧ p ≡ a₁ [MOD n₁] ∧ p ≡ a₂ [MOD n₂] := by

  obtain ⟨k, hk₁, hk₂⟩ := Nat.chineseRemainder hcop a₁ a₂

  have h1 : k.Coprime n₁ := by
    unfold Nat.Coprime
    rw [hk₁.gcd_eq]
    exact ha₁
  have h2 : k.Coprime n₂ := by
    unfold Nat.Coprime
    rw [hk₂.gcd_eq]
    exact ha₂
  have hkcop : k.Coprime (n₁ * n₂) := Nat.Coprime.mul_right h1 h2

  obtain ⟨p, hpN, hpp, hp⟩ := Nat.forall_exists_prime_gt_and_modEq (max N 2)
    (mul_ne_zero hn₁ hn₂) hkcop
  refine ⟨p, lt_of_le_of_lt (le_max_left N 2) hpN, hpp, hpp.odd_of_ne_two ?_, ?_, ?_⟩
  · have h2p : 2 < p := lt_of_le_of_lt (le_max_right N 2) hpN
    omega
  · exact (hp.of_dvd (dvd_mul_right n₁ n₂)).trans hk₁
  · exact (hp.of_dvd (dvd_mul_left n₂ n₁)).trans hk₂

end DirichletSteps

section ArithmeticEngine

theorem mennicke_lifting_step {y M : ℤ} {ℓ : ℕ} (hℓM : (ℓ : ℤ) ∣ M)
    (hy : M ∣ y - 1) : (M * ℓ) ∣ y ^ ℓ - 1 := by
  rw [← geom_sum_mul y ℓ]
  have hℓy : (ℓ : ℤ) ∣ y - 1 := hℓM.trans hy
  have hsum : (ℓ : ℤ) ∣ ∑ i ∈ Finset.range ℓ, y ^ i := by
    have h1 : ∀ i ∈ Finset.range ℓ, (ℓ : ℤ) ∣ y ^ i - 1 := fun i _ =>
      hℓy.trans (sub_one_dvd_pow_sub_one y i)
    have h2 : (ℓ : ℤ) ∣ ∑ i ∈ Finset.range ℓ, (y ^ i - 1) := Finset.dvd_sum h1
    have h3 : ∑ i ∈ Finset.range ℓ, (y ^ i - 1) =
        (∑ i ∈ Finset.range ℓ, y ^ i) - (ℓ : ℤ) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        mul_one]
    rw [h3] at h2
    have h4 := dvd_add h2 (dvd_refl (ℓ : ℤ))
    rwa [sub_add_cancel] at h4
  rw [mul_comm M (ℓ : ℤ)]
  exact mul_dvd_mul hsum hy

theorem mennicke_lifting_iterate {y : ℤ} {ℓ f : ℕ} (hf : 1 ≤ f)
    (hy : ((ℓ : ℤ) ^ f) ∣ y - 1) (k : ℕ) :
    ((ℓ : ℤ) ^ (f + k)) ∣ y ^ ℓ ^ k - 1 := by
  induction k with
  | zero => simpa using hy
  | succ k ih =>
    have hstep : ((ℓ : ℤ) ^ (f + k) * ℓ) ∣ (y ^ ℓ ^ k) ^ ℓ - 1 :=
      mennicke_lifting_step (dvd_pow_self (ℓ : ℤ) (by omega : f + k ≠ 0)) ih
    have h1 : (ℓ : ℤ) ^ (f + k) * ℓ = (ℓ : ℤ) ^ (f + (k + 1)) := by
      rw [show f + (k + 1) = (f + k) + 1 by omega, pow_succ]
    have h2 : (y ^ ℓ ^ k) ^ ℓ = y ^ ℓ ^ (k + 1) := by
      rw [← pow_mul, ← pow_succ]
    rwa [h1, h2] at hstep

theorem mennicke_two_twentyone_of_corrected_reading (x m : ℕ) (hx : 2 ≤ x) (hm : m ≠ 0)
    (hdvd : (x - 1) ∣ m) (hsupp : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ m → ℓ ∣ (x - 1)) :
    m ∣ x ^ (m / (x - 1)) - 1 := by
  have hd0 : x - 1 ≠ 0 := by omega
  have hx1 : (1 : ℕ) ≤ x := by omega

  have hu : 0 < m / (x - 1) :=
    Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hm) hdvd) (by omega)

  have hXgt : 1 < x ^ (m / (x - 1)) :=
    lt_of_lt_of_le (by omega : (1 : ℕ) < x) (Nat.le_self_pow (by omega) x)
  have hX0 : x ^ (m / (x - 1)) - 1 ≠ 0 := by omega

  rw [← Nat.factorization_le_iff_dvd hm hX0, Finsupp.le_iff]
  intro ℓ hℓsupp
  rw [Nat.support_factorization, Nat.mem_primeFactors] at hℓsupp
  obtain ⟨hℓp, hℓm, -⟩ := hℓsupp

  set e := m.factorization ℓ with he
  set f := (x - 1).factorization ℓ with hf

  have hℓd : ℓ ∣ x - 1 := hsupp ℓ hℓp hℓm
  have hf1 : 1 ≤ f := hℓp.factorization_pos_of_dvd hd0 hℓd

  have hfact_le : (x - 1).factorization ≤ m.factorization :=
    (Nat.factorization_le_iff_dvd hd0 hm).mpr hdvd
  have hfe : f ≤ e := Finsupp.le_def.mp hfact_le ℓ

  have hpf_nat : ℓ ^ f ∣ x - 1 := Nat.ordProj_dvd (x - 1) ℓ
  have hpf_int : ((ℓ : ℤ)) ^ f ∣ (x : ℤ) - 1 := by
    have h := Int.natCast_dvd_natCast.mpr hpf_nat
    rwa [Nat.cast_pow, Nat.cast_sub hx1, Nat.cast_one] at h

  have hlift : ((ℓ : ℤ)) ^ e ∣ (x : ℤ) ^ ℓ ^ (e - f) - 1 := by
    have h := mennicke_lifting_iterate hf1 hpf_int (e - f)
    rwa [Nat.add_sub_cancel' hfe] at h

  have hu_fact : (m / (x - 1)).factorization ℓ = e - f := by
    rw [Nat.factorization_div hdvd, Finsupp.tsub_apply]
  have hdvd_u : ℓ ^ (e - f) ∣ m / (x - 1) := by
    rw [← hu_fact]
    exact Nat.ordProj_dvd _ _

  have hchain : (x : ℤ) ^ ℓ ^ (e - f) - 1 ∣ (x : ℤ) ^ (m / (x - 1)) - 1 :=
    dvd_pow_sub_one_of_dvd hdvd_u

  have hint : ((ℓ : ℤ)) ^ e ∣ (x : ℤ) ^ (m / (x - 1)) - 1 := hlift.trans hchain
  have hnat : ℓ ^ e ∣ x ^ (m / (x - 1)) - 1 := by
    have hcast : ((x ^ (m / (x - 1)) - 1 : ℕ) : ℤ) = (x : ℤ) ^ (m / (x - 1)) - 1 := by
      rw [Nat.cast_sub (le_of_lt hXgt), Nat.cast_pow, Nat.cast_one]
    rw [← Int.natCast_dvd_natCast, hcast, Nat.cast_pow]
    exact hint
  exact (hℓp.pow_dvd_iff_le_factorization hX0).mp hnat

theorem mennicke_two_thirty_implies_two_twentyone (q m : ℕ) (hq : 2 ≤ q) (hm : m ≠ 0)
    (hdvd : (q ^ 2 - 1) ∣ m) (hsupp : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ m → ℓ ∣ (q ^ 2 - 1)) :
    m ∣ q ^ (2 * (m / (q ^ 2 - 1))) - 1 := by
  have hx : 2 ≤ q ^ 2 := le_trans hq (Nat.le_self_pow (by omega) q)
  have h := mennicke_two_twentyone_of_corrected_reading (q ^ 2) m hx hm hdvd hsupp
  rwa [pow_mul]

theorem mennicke_two_thirtythree_fermat_choice (ϱ : ℕ) (hϱ : ϱ.Prime) (hodd : Odd ϱ)
    (x : ℕ) (hx : x.Coprime ϱ) :
    ∃ r : ℕ, 2 * r = ϱ - 1 ∧ x ^ (2 * r) ≡ 1 [MOD ϱ] := by
  obtain ⟨t, ht⟩ := hodd
  refine ⟨t, by omega, ?_⟩
  have h1 : x ^ Nat.totient ϱ ≡ 1 [MOD ϱ] := Nat.ModEq.pow_totient hx
  rw [Nat.totient_prime hϱ] at h1
  have h2 : 2 * t = ϱ - 1 := by omega
  rwa [h2]

end ArithmeticEngine

section TwoFourteen

variable (q m : ℕ) [NeZero q]

end TwoFourteen

section DiophantineCarrier

def MennickeDiophantineSolutionAt (q m u : ℕ) : Prop :=
  ∀ a b : ℤ, a ≠ 0 → b ≠ 0 → IsCoprime a b → IsCoprime a (m : ℤ) →
    ∃ (r : ℕ) (y t : ℤ),
      (b + a * y) * (m : ℤ) * t = a * ((q : ℤ) ^ (2 * (r * u)) - 1) ∧
      IsCoprime t (m : ℤ)

end DiophantineCarrier

section Headline

variable (q m : ℕ) [NeZero q]

end Headline

section CorrectedReading

variable (q m : ℕ) [NeZero q]

end CorrectedReading

end

end Ihara

namespace Ihara
p2m_export "Ihara" "mennickeZ_eq_top_of_corrected_reading_of_diophantine mennickeZ"
p2m_open "Ihara"

open Subgroup

noncomputable section

section Helpers

theorem mennicke_natCast_pow_sub_one {q : ℕ} (hq : 1 ≤ q) (n : ℕ) :
    ((q ^ n - 1 : ℕ) : ℤ) = (q : ℤ) ^ n - 1 := by
  have h : 1 ≤ q ^ n := Nat.one_le_pow n q hq
  push_cast [h]
  ring

theorem mennicke_nat_pow_sub_one_dvd {x : ℕ} (hx : 1 ≤ x) {a b : ℕ} (hab : a ∣ b) :
    x ^ a - 1 ∣ x ^ b - 1 := by
  rw [← Int.natCast_dvd_natCast, mennicke_natCast_pow_sub_one hx,
    mennicke_natCast_pow_sub_one hx]
  exact dvd_pow_sub_one_of_dvd hab

end Helpers

section TwoTwentyNine

theorem mennicke_two_twentynine (m : ℕ) (hm : m ≠ 0) (a b : ℤ) (ha : a ≠ 0)
    (hab : IsCoprime a b) (ham : IsCoprime a (m : ℤ)) (N : ℕ) :
    ∃ (ϱ : ℕ) (y : ℤ), N < ϱ ∧ ϱ.Prime ∧ Odd ϱ ∧ m ∣ ϱ + 1 ∧ b + a * y = -(ϱ : ℤ) := by

  have hA : a.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr ha
  have hA_int_ne : ((a.natAbs : ℕ) : ℤ) ≠ 0 := by exact_mod_cast hA

  have hcop : a.natAbs.Coprime m := by
    have h := Int.isCoprime_iff_gcd_eq_one.mp ham
    rwa [Int.gcd_def, Int.natAbs_natCast] at h

  have he_nonneg : 0 ≤ (-b) % (a.natAbs : ℤ) := Int.emod_nonneg (-b) hA_int_ne
  have hdvd_be : ((a.natAbs : ℕ) : ℤ) ∣ (-b) - (-b) % (a.natAbs : ℤ) := by
    refine ⟨(-b) / (a.natAbs : ℤ), ?_⟩
    have h := Int.emod_add_mul_ediv (-b) (a.natAbs : ℤ)
    linarith

  have hβ_cast : ((((-b) % (a.natAbs : ℤ)).toNat : ℕ) : ℤ) = (-b) % (a.natAbs : ℤ) :=
    Int.toNat_of_nonneg he_nonneg

  have hβ_cop : ((-b) % (a.natAbs : ℤ)).toNat.Coprime a.natAbs := by
    rw [← Nat.isCoprime_iff_coprime, hβ_cast]

    obtain ⟨k, hk⟩ := hdvd_be
    have he_eq : (-b) % (a.natAbs : ℤ) = (-b) + ((a.natAbs : ℕ) : ℤ) * (-k) := by
      linarith
    rw [he_eq]

    have h1 : IsCoprime (-b) a := (hab.symm).neg_left
    have h2 : IsCoprime (-b) ((a.natAbs : ℕ) : ℤ) := by
      rcases Int.natAbs_eq a with h | h
      · rwa [← h]
      ·
        have h3 : ((a.natAbs : ℕ) : ℤ) = -a := by linarith
        rw [h3]
        exact h1.neg_right

    exact h2.add_mul_left_left (-k)

  have hm1_cop : (m - 1).Coprime m := by
    have h1 : 1 ≤ m := Nat.pos_of_ne_zero hm
    exact (Nat.coprime_self_sub_left h1).mpr (Nat.coprime_one_left m)

  obtain ⟨ϱ, hϱN, hϱp, hϱodd, hϱ₁, hϱ₂⟩ :=
    dirichlet_exists_odd_prime_modEq_pair a.natAbs m hA hm hcop
      ((-b) % (a.natAbs : ℤ)).toNat (m - 1) hβ_cop hm1_cop N

  have hm_dvd : m ∣ ϱ + 1 := by
    have h1 : ϱ + 1 ≡ (m - 1) + 1 [MOD m] := hϱ₂.add_right 1
    have h2 : m - 1 + 1 = m := by omega
    rw [h2] at h1
    have h3 : ϱ + 1 ≡ 0 [MOD m] := h1.trans (Nat.modEq_zero_iff_dvd.mpr dvd_rfl)
    exact Nat.modEq_zero_iff_dvd.mp h3

  have ha_dvd : a ∣ b + (ϱ : ℕ) := by

    have h1 : ((a.natAbs : ℕ) : ℤ) ∣
        ((((-b) % (a.natAbs : ℤ)).toNat : ℕ) : ℤ) - ((ϱ : ℕ) : ℤ) :=
      Nat.modEq_iff_dvd.mp hϱ₁
    rw [hβ_cast] at h1

    have h2 : ((a.natAbs : ℕ) : ℤ) ∣ (-b) - ((ϱ : ℕ) : ℤ) := by
      have h3 := dvd_add hdvd_be h1
      have heq : ((-b) - (-b) % (a.natAbs : ℤ)) +
          ((-b) % (a.natAbs : ℤ) - ((ϱ : ℕ) : ℤ)) = (-b) - ((ϱ : ℕ) : ℤ) := by ring
      rwa [heq] at h3

    have h4 : a ∣ (-b) - ((ϱ : ℕ) : ℤ) := Int.natAbs_dvd.mp h2
    have h5 : a ∣ -((-b) - ((ϱ : ℕ) : ℤ)) := dvd_neg.mpr h4
    have heq : -((-b) - ((ϱ : ℕ) : ℤ)) = b + ((ϱ : ℕ) : ℤ) := by ring
    rwa [heq] at h5
  obtain ⟨y', hy'⟩ := ha_dvd
  exact ⟨ϱ, -y', hϱN, hϱp, hϱodd, hm_dvd, by linear_combination hy'⟩

end TwoTwentyNine

section TwoThirtyOne

theorem mennicke_two_thirtyone (q m : ℕ) (hq : 2 ≤ q) (hm : m ≠ 0)
    (hdvd : (q ^ 2 - 1) ∣ m) (hsupp : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ m → ℓ ∣ (q ^ 2 - 1))
    (r : ℕ) :
    m ∣ q ^ (2 * r * (m / (q ^ 2 - 1))) - 1 := by
  have h21 := mennicke_two_thirty_implies_two_twentyone q m hq hm hdvd hsupp
  exact h21.trans (mennicke_nat_pow_sub_one_dvd (by omega) ⟨r, by ring⟩)

end TwoThirtyOne

section TwoThirtyTwoThirtyThree

theorem mennicke_two_thirtytwo_thirtythree (q ϱ : ℕ) (hq : 1 ≤ q) (hϱ : ϱ.Prime)
    (hodd : Odd ϱ) (hqϱ : q.Coprime ϱ) (u : ℕ) :
    ∃ r : ℕ, 2 * r = ϱ - 1 ∧ ϱ ∣ q ^ (2 * r * u) - 1 := by
  obtain ⟨r, hr, hferm⟩ := mennicke_two_thirtythree_fermat_choice ϱ hϱ hodd q hqϱ
  refine ⟨r, hr, ?_⟩
  have h1 : 1 ≤ q ^ (2 * r) := Nat.one_le_pow _ _ hq
  have h2 : ϱ ∣ q ^ (2 * r) - 1 := (Nat.modEq_iff_dvd' h1).mp hferm.symm
  exact h2.trans (mennicke_nat_pow_sub_one_dvd hq ⟨u, by ring⟩)

end TwoThirtyTwoThirtyThree

section TwoThirtyFour

theorem mennicke_two_thirtyfour (q m : ℕ) (hq : 2 ≤ q)
    (hdvd : (q ^ 2 - 1) ∣ m) (hsupp : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ m → ℓ ∣ (q ^ 2 - 1))
    (ϱ r : ℕ) (hϱ1 : 1 ≤ ϱ) (hϱm : m ∣ ϱ + 1) (hr : 2 * r = ϱ - 1) :
    Nat.Coprime r m := by
  have hϱ_eq : ϱ = 2 * r + 1 := by omega

  have hgcd_r : Nat.gcd r m ∣ r := Nat.gcd_dvd_left r m
  have hgcd_m : Nat.gcd r m ∣ m := Nat.gcd_dvd_right r m
  have hgcd2 : Nat.gcd r m ∣ 2 := by
    have h3 : Nat.gcd r m ∣ ϱ + 1 := hgcd_m.trans hϱm
    have h4 : Nat.gcd r m ∣ 2 * r := hgcd_r.mul_left 2
    have h5 := Nat.dvd_sub h3 h4
    have h6 : ϱ + 1 - 2 * r = 2 := by omega
    rwa [h6] at h5

  rcases (Nat.dvd_prime Nat.prime_two).mp hgcd2 with h | h
  · exact h
  · exfalso
    rcases Nat.even_or_odd q with hqe | hqo
    ·
      have h2m : (2 : ℕ) ∣ m := h ▸ hgcd_m
      have h2q21 : (2 : ℕ) ∣ q ^ 2 - 1 := hsupp 2 Nat.prime_two h2m
      obtain ⟨k, hk⟩ := hqe
      have h2q : (2 : ℕ) ∣ q := ⟨k, by omega⟩
      have h2q2 : (2 : ℕ) ∣ q ^ 2 := dvd_pow h2q (by omega)
      have hq2_ge : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
      have h21 : (2 : ℕ) ∣ q ^ 2 - (q ^ 2 - 1) := Nat.dvd_sub h2q2 h2q21
      have heq : q ^ 2 - (q ^ 2 - 1) = 1 := by omega
      rw [heq] at h21
      omega
    ·
      have h2r : (2 : ℕ) ∣ r := h ▸ hgcd_r
      have h8 : (8 : ℕ) ∣ q ^ 2 - 1 := Nat.eight_dvd_sq_sub_one_of_odd hqo
      have h8m : (8 : ℕ) ∣ m := h8.trans hdvd
      have h4m : (4 : ℕ) ∣ m := dvd_trans (by norm_num) h8m
      have h4ϱ : (4 : ℕ) ∣ ϱ + 1 := h4m.trans hϱm
      rw [hϱ_eq] at h4ϱ
      omega

end TwoThirtyFour

section LTEExactValuation

theorem mennicke_lte_exact_valuation (q u ℓ : ℕ) (hq : 2 ≤ q) (hu : u ≠ 0)
    (hℓ : ℓ.Prime) (hℓdvd : ℓ ∣ q ^ 2 - 1) :
    padicValNat ℓ (q ^ (2 * u) - 1) = padicValNat ℓ (q ^ 2 - 1) + padicValNat ℓ u := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hq2 : 1 < q ^ 2 := by
    have hmul : 2 * 2 ≤ q * q := Nat.mul_le_mul hq hq
    have hsq : q ^ 2 = q * q := by ring
    omega

  have hℓq2 : ¬ ℓ ∣ q ^ 2 := by
    intro hcon
    have h1 : ℓ ∣ q ^ 2 - (q ^ 2 - 1) := Nat.dvd_sub hcon hℓdvd
    have h2 : q ^ 2 - (q ^ 2 - 1) = 1 := by omega
    rw [h2] at h1
    have h3 := Nat.le_of_dvd (by omega) h1
    have h4 := hℓ.two_le
    omega
  rcases hℓ.eq_two_or_odd' with hℓ2 | hℓodd
  ·
    subst hℓ2
    have hq_odd : ¬ (2 : ℕ) ∣ q := fun h2q => hℓq2 (dvd_pow h2q (by omega))
    have hlte := padicValNat.pow_two_sub_one (x := q) (n := 2 * u) (by omega) hq_odd
      (by omega) (even_two_mul u)

    have hfact : q ^ 2 - 1 = (q + 1) * (q - 1) := by
      have h := Nat.pow_two_sub_pow_two q 1
      rwa [one_pow] at h
    have hsplit : padicValNat 2 (q ^ 2 - 1) =
        padicValNat 2 (q + 1) + padicValNat 2 (q - 1) := by
      rw [hfact]
      exact padicValNat.mul (by omega) (by omega)

    have h2u : padicValNat 2 (2 * u) = 1 + padicValNat 2 u := by
      rw [padicValNat.mul (by omega) hu, padicValNat_self]
    omega
  ·
    have hlte := padicValNat.pow_sub_pow (p := ℓ) hℓodd (x := q ^ 2) (y := 1)
      hq2 hℓdvd hℓq2 hu
    rw [one_pow, ← pow_mul] at hlte
    exact hlte

end LTEExactValuation

section TwoThirtyFiveThirtySix

theorem mennicke_two_thirtyfive (q u r : ℕ) (hq : 1 ≤ q) :
    q ^ (2 * r * u) - 1 =
      (q ^ (2 * u) - 1) * ∑ i ∈ Finset.range r, (q ^ (2 * u)) ^ i := by
  have h1 : 1 ≤ q ^ (2 * u) := Nat.one_le_pow _ _ hq
  have h2 : 1 ≤ q ^ (2 * r * u) := Nat.one_le_pow _ _ hq
  have key : ((q ^ (2 * r * u) - 1 : ℕ) : ℤ) =
      (((q ^ (2 * u) - 1) * ∑ i ∈ Finset.range r, (q ^ (2 * u)) ^ i : ℕ) : ℤ) := by
    push_cast [h1, h2]
    have hexp : 2 * r * u = 2 * u * r := by ring
    rw [hexp, mul_geom_sum, ← pow_mul]
  exact_mod_cast key

theorem mennicke_geom_sum_coprime (x r m : ℕ) (hx1 : 1 ≤ x) (hx : m ∣ x - 1)
    (hrm : Nat.Coprime r m) :
    Nat.Coprime (∑ i ∈ Finset.range r, x ^ i) m := by
  by_contra hne
  obtain ⟨ℓ, hℓp, hℓdvd⟩ := Nat.exists_prime_and_dvd hne
  have hℓS : ℓ ∣ ∑ i ∈ Finset.range r, x ^ i := hℓdvd.trans (Nat.gcd_dvd_left _ _)
  have hℓm : ℓ ∣ m := hℓdvd.trans (Nat.gcd_dvd_right _ _)

  have hℓx : ℓ ∣ x - 1 := hℓm.trans hx
  have hℓx_int : (ℓ : ℤ) ∣ (x : ℤ) - 1 := by
    have h := Int.natCast_dvd_natCast.mpr hℓx
    rwa [Nat.cast_sub hx1, Nat.cast_one] at h

  have hsum_sub : (ℓ : ℤ) ∣ (∑ i ∈ Finset.range r, (x : ℤ) ^ i) - r := by
    have h1 : ∀ i ∈ Finset.range r, (ℓ : ℤ) ∣ (x : ℤ) ^ i - 1 := fun i _ =>
      hℓx_int.trans (sub_one_dvd_pow_sub_one (x : ℤ) i)
    have h2 : (ℓ : ℤ) ∣ ∑ i ∈ Finset.range r, ((x : ℤ) ^ i - 1) := Finset.dvd_sum h1
    have h3 : ∑ i ∈ Finset.range r, ((x : ℤ) ^ i - 1) =
        (∑ i ∈ Finset.range r, (x : ℤ) ^ i) - r := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        mul_one]
    rwa [h3] at h2

  have hℓS_int : (ℓ : ℤ) ∣ ∑ i ∈ Finset.range r, (x : ℤ) ^ i := by
    have h := Int.natCast_dvd_natCast.mpr hℓS
    push_cast at h
    exact h

  have hℓr_int : (ℓ : ℤ) ∣ (r : ℤ) := by
    have h := dvd_sub hℓS_int hsum_sub
    have heq : (∑ i ∈ Finset.range r, (x : ℤ) ^ i) -
        ((∑ i ∈ Finset.range r, (x : ℤ) ^ i) - r) = (r : ℤ) := by ring
    rwa [heq] at h
  have hℓr : ℓ ∣ r := Int.natCast_dvd_natCast.mp hℓr_int
  have hcontra : ℓ ∣ Nat.gcd r m := Nat.dvd_gcd hℓr hℓm
  have hgcd1 : Nat.gcd r m = 1 := hrm
  rw [hgcd1] at hcontra
  have h1 := Nat.le_of_dvd (by omega) hcontra
  have h2 := hℓp.two_le
  omega

theorem mennicke_two_thirtysix (q m : ℕ) (hq : 2 ≤ q) (hm : m ≠ 0)
    (hdvd : (q ^ 2 - 1) ∣ m) (hsupp : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ m → ℓ ∣ (q ^ 2 - 1)) :
    Nat.Coprime ((q ^ (2 * (m / (q ^ 2 - 1))) - 1) / m) m := by

  have hq21_pos : 0 < q ^ 2 - 1 := by
    have hmul : 2 * 2 ≤ q * q := Nat.mul_le_mul hq hq
    have hsq : q ^ 2 = q * q := by ring
    omega
  have hu_pos : 0 < m / (q ^ 2 - 1) :=
    Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hm) hdvd) hq21_pos
  have hu_ne : m / (q ^ 2 - 1) ≠ 0 := hu_pos.ne'

  have hm_eq : (q ^ 2 - 1) * (m / (q ^ 2 - 1)) = m := Nat.mul_div_cancel' hdvd

  have h21 : m ∣ q ^ (2 * (m / (q ^ 2 - 1))) - 1 :=
    mennicke_two_thirty_implies_two_twentyone q m hq hm hdvd hsupp
  have hD_eq : m * ((q ^ (2 * (m / (q ^ 2 - 1))) - 1) / m) =
      q ^ (2 * (m / (q ^ 2 - 1))) - 1 := Nat.mul_div_cancel' h21

  have hpow1 : 1 < q ^ (2 * (m / (q ^ 2 - 1))) := by
    have h1 : 1 < q ^ 2 := by
      have hmul : 2 * 2 ≤ q * q := Nat.mul_le_mul hq hq
      have hsq : q ^ 2 = q * q := by ring
      omega
    calc 1 < q ^ 2 := h1
      _ ≤ q ^ (2 * (m / (q ^ 2 - 1))) := Nat.pow_le_pow_right (by omega) (by omega)
  have hD_ne : (q ^ (2 * (m / (q ^ 2 - 1))) - 1) / m ≠ 0 := by
    intro hD0
    rw [hD0, Nat.mul_zero] at hD_eq
    omega

  by_contra hne
  obtain ⟨ℓ, hℓp, hℓdvd_gcd⟩ := Nat.exists_prime_and_dvd hne
  haveI : Fact ℓ.Prime := ⟨hℓp⟩
  have hℓD : ℓ ∣ (q ^ (2 * (m / (q ^ 2 - 1))) - 1) / m :=
    hℓdvd_gcd.trans (Nat.gcd_dvd_left _ _)
  have hℓm : ℓ ∣ m := hℓdvd_gcd.trans (Nat.gcd_dvd_right _ _)
  have hℓq21 : ℓ ∣ q ^ 2 - 1 := hsupp ℓ hℓp hℓm

  have hlte := mennicke_lte_exact_valuation q (m / (q ^ 2 - 1)) ℓ hq hu_ne hℓp hℓq21
  have hval1 : padicValNat ℓ (q ^ (2 * (m / (q ^ 2 - 1))) - 1) =
      padicValNat ℓ m + padicValNat ℓ ((q ^ (2 * (m / (q ^ 2 - 1))) - 1) / m) := by

    conv_lhs => rw [← hD_eq]
    exact padicValNat.mul hm hD_ne
  have hval2 : padicValNat ℓ m =
      padicValNat ℓ (q ^ 2 - 1) + padicValNat ℓ (m / (q ^ 2 - 1)) := by

    conv_lhs => rw [← hm_eq]
    exact padicValNat.mul (by omega) hu_ne
  have hvalD : 1 ≤ padicValNat ℓ ((q ^ (2 * (m / (q ^ 2 - 1))) - 1) / m) :=
    one_le_padicValNat_of_dvd hD_ne hℓD
  omega

theorem mennicke_quotient_coprime (q m ϱ r u c : ℕ) (hq : 2 ≤ q) (hm : m ≠ 0)
    (h21 : m ∣ q ^ (2 * u) - 1)
    (h36 : Nat.Coprime ((q ^ (2 * u) - 1) / m) m)
    (h34 : Nat.Coprime r m)
    (hc : q ^ (2 * r * u) - 1 = ϱ * m * c) :
    Nat.Coprime c m := by

  have h35_eq : q ^ (2 * r * u) - 1 =
      (q ^ (2 * u) - 1) * ∑ i ∈ Finset.range r, (q ^ (2 * u)) ^ i :=
    mennicke_two_thirtyfive q u r (by omega)

  have h35_cop : Nat.Coprime (∑ i ∈ Finset.range r, (q ^ (2 * u)) ^ i) m :=
    mennicke_geom_sum_coprime (q ^ (2 * u)) r m (Nat.one_le_pow _ _ (by omega)) h21 h34

  have hD_eq : m * ((q ^ (2 * u) - 1) / m) = q ^ (2 * u) - 1 := Nat.mul_div_cancel' h21

  have hkey : ϱ * c =
      ((q ^ (2 * u) - 1) / m) * ∑ i ∈ Finset.range r, (q ^ (2 * u)) ^ i := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hm)
    calc m * (ϱ * c) = ϱ * m * c := by ring
      _ = q ^ (2 * r * u) - 1 := hc.symm
      _ = (q ^ (2 * u) - 1) * ∑ i ∈ Finset.range r, (q ^ (2 * u)) ^ i := h35_eq
      _ = (m * ((q ^ (2 * u) - 1) / m)) * ∑ i ∈ Finset.range r, (q ^ (2 * u)) ^ i := by
          rw [hD_eq]
      _ = m * (((q ^ (2 * u) - 1) / m) * ∑ i ∈ Finset.range r, (q ^ (2 * u)) ^ i) := by
          ring

  have hc_dvd : c ∣ ((q ^ (2 * u) - 1) / m) * ∑ i ∈ Finset.range r, (q ^ (2 * u)) ^ i :=
    ⟨ϱ, by rw [← hkey]; ring⟩
  have hprod_cop : Nat.Coprime
      (((q ^ (2 * u) - 1) / m) * ∑ i ∈ Finset.range r, (q ^ (2 * u)) ^ i) m :=
    (Nat.Coprime.mul_right h36.symm h35_cop.symm).symm
  exact Nat.Coprime.coprime_dvd_left hc_dvd hprod_cop

end TwoThirtyFiveThirtySix

section Headline

def MennickeDiophantineSolution (q m : ℕ) (a b : ℤ) (u : ℕ) : Prop :=
  ∃ (y t : ℤ) (r : ℕ), 0 < r ∧
    (b + a * y) * (m : ℤ) * t = a * ((q : ℤ) ^ (2 * r * u) - 1) ∧
    IsCoprime t (m : ℤ)

theorem mennickeDiophantineSolution_holds (q m : ℕ) (hq : 2 ≤ q) (hm : m ≠ 0)
    (hdvd : (q ^ 2 - 1) ∣ m) (hsupp : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ m → ℓ ∣ (q ^ 2 - 1))
    (a b : ℤ) (ha : a ≠ 0) (hab : IsCoprime a b) (ham : IsCoprime a (m : ℤ)) :
    MennickeDiophantineSolution q m a b (m / (q ^ 2 - 1)) := by

  obtain ⟨ϱ, y, hϱN, hϱp, hϱodd, hϱ_cong, hby⟩ :=
    mennicke_two_twentynine m hm a b ha hab ham (max q m)
  have hϱ_gt_q : q < ϱ := lt_of_le_of_lt (le_max_left q m) hϱN
  have hϱ_gt_m : m < ϱ := lt_of_le_of_lt (le_max_right q m) hϱN

  have hqϱ : q.Coprime ϱ := by
    have hnd : ¬ ϱ ∣ q := fun hd => absurd (Nat.le_of_dvd (by omega) hd) (by omega)
    exact ((Nat.Prime.coprime_iff_not_dvd hϱp).mpr hnd).symm
  obtain ⟨r, hr_eq, hr_dvd⟩ :=
    mennicke_two_thirtytwo_thirtythree q ϱ (by omega) hϱp hϱodd hqϱ (m / (q ^ 2 - 1))

  have hϱ3 : 3 ≤ ϱ := by
    obtain ⟨k, hk⟩ := hϱodd
    have h2 := hϱp.two_le
    omega
  have hr_pos : 0 < r := by omega

  have h34 : Nat.Coprime r m :=
    mennicke_two_thirtyfour q m hq hdvd hsupp ϱ r (by omega) hϱ_cong hr_eq

  have h_m_dvd : m ∣ q ^ (2 * r * (m / (q ^ 2 - 1))) - 1 :=
    mennicke_two_thirtyone q m hq hm hdvd hsupp r
  have hϱm_cop : ϱ.Coprime m := by
    have hnd : ¬ ϱ ∣ m := fun hd =>
      absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hm) hd) (by omega)
    exact (Nat.Prime.coprime_iff_not_dvd hϱp).mpr hnd
  have h_ϱm_dvd : ϱ * m ∣ q ^ (2 * r * (m / (q ^ 2 - 1))) - 1 :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd hϱm_cop hr_dvd h_m_dvd
  obtain ⟨c, hc⟩ := h_ϱm_dvd

  have h21 : m ∣ q ^ (2 * (m / (q ^ 2 - 1))) - 1 :=
    mennicke_two_thirty_implies_two_twentyone q m hq hm hdvd hsupp
  have h36 : Nat.Coprime ((q ^ (2 * (m / (q ^ 2 - 1))) - 1) / m) m :=
    mennicke_two_thirtysix q m hq hm hdvd hsupp
  have hc_cop : Nat.Coprime c m :=
    mennicke_quotient_coprime q m ϱ r (m / (q ^ 2 - 1)) c hq hm h21 h36 h34 hc

  refine ⟨y, -(a * (c : ℕ)), r, hr_pos, ?_, ?_⟩
  ·
    rw [hby]
    have hcast : ((q ^ (2 * r * (m / (q ^ 2 - 1))) - 1 : ℕ) : ℤ) =
        (q : ℤ) ^ (2 * r * (m / (q ^ 2 - 1))) - 1 :=
      mennicke_natCast_pow_sub_one (by omega) _
    rw [← hcast, hc]
    push_cast
    ring
  ·
    exact ((ham.mul_left (Nat.Coprime.isCoprime hc_cop)).neg_left)

end Headline

theorem ihxw14_dio_solutionAt_saturated (q : ℕ) (hq : 2 ≤ q) :
    ∀ m : ℕ, Nat.Coprime m q → (q ^ 2 - 1) ∣ m →
      (∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ m → ℓ ∣ (q ^ 2 - 1)) →
      MennickeDiophantineSolutionAt q m (m / (q ^ 2 - 1)) := by
  intro m hmq hdvd hsupp a b ha _hb hab ham

  have hm : m ≠ 0 := by
    rintro rfl
    rw [Nat.coprime_zero_left] at hmq
    omega

  obtain ⟨y, t, r, _hr_pos, h17, h25⟩ :=
    mennickeDiophantineSolution_holds q m hq hm hdvd hsupp a b ha hab ham

  refine ⟨r, y, t, ?_, h25⟩
  rw [mul_assoc 2 r] at h17
  exact h17

theorem ihxw14_dio_lemma22_statement_unconditional_impl (q : ℕ) [NeZero q] (hq : 2 ≤ q) :
    ∀ m : ℕ, ∀ hmq : Nat.Coprime m q, (q ^ 2 - 1) ∣ m →
      (∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ m → ℓ ∣ (q ^ 2 - 1)) →
      mennickeZ q m hmq = ⊤ :=
  fun m hmq hdvd hsupp =>
    mennickeZ_eq_top_of_corrected_reading_of_diophantine q m hmq hq hdvd hsupp
      (ihxw14_dio_solutionAt_saturated q hq m hmq hdvd hsupp)

end

end Ihara

open scoped MatrixGroups commutatorElement in
open _root_.Ihara _root_.P2MW.S_Ihara_ihxw14_dio_lemma22_statement_unconditional.Ihara in
theorem solution (q : ℕ) [NeZero q] (hq : 2 ≤ q) :
    ∀ m : ℕ, ∀ hmq : Nat.Coprime m q, (q ^ 2 - 1) ∣ m →
      (∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ m → ℓ ∣ (q ^ 2 - 1)) →
      Ihara.mennickeZ q m hmq = ⊤ :=
  Ihara.ihxw14_dio_lemma22_statement_unconditional_impl q hq

#print axioms solution

end S_Ihara_ihxw14_dio_lemma22_statement_unconditional
end P2MW
export P2MW.S_Ihara_ihxw14_dio_lemma22_statement_unconditional (solution)
