-- Prove2me | solution 1 for Ihara.hasTrivialSchurMultiplier_SL2_ZMod_sq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/eec48a35-6dce-5384-a9dd-b92ead7c66e2

import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Module
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.GroupTheory.Coset.Card
import Theorems.Thm_Ihara_ker_eq_bot_of_stem_of_fibre
import Theorems.Thm_Ihara_sl2_zmod_sq_congruence_preimage_commute
import Theorems.Thm_Ihara_ker_pow_eq_one_of_stem
import Definitions.Def_SchurMultiplierTrivial
import Mathlib.Tactic.LinearCombination
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.Data.Int.GCD
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_sq

section Inl_W5_RemintA

namespace Ihara
p2m_export "Ihara" "ker_eq_bot_of_stem_of_fibre sl2_zmod_sq_congruence_preimage_commute ker_pow_eq_one_of_stem HasTrivialSchurMultiplier"
p2m_open "Ihara"

open Matrix
open scoped MatrixGroups

private theorem sl2coe_mul_w5 {R : Type*} [CommRing R] (A B : SL(2, R)) :
    ((A * B : SL(2, R)) : Matrix (Fin 2) (Fin 2) R)
      = (A : Matrix (Fin 2) (Fin 2) R) * B := rfl

theorem one_add_smul_pow {R : Type*} [CommRing R] (m : ℕ) (x : R)
    (A : Matrix (Fin 2) (Fin 2) R) :
    ∃ B : Matrix (Fin 2) (Fin 2) R,
      (1 + x • A) ^ m = 1 + ((m : R) * x) • A + x ^ 2 • B := by
  induction m with
  | zero => exact ⟨0, by simp⟩
  | succ l ih =>
    obtain ⟨B, hB⟩ := ih
    refine ⟨(l : R) • (A * A) + B + x • (B * A), ?_⟩
    rw [_root_.pow_succ, hB]
    simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm,
      smul_add, smul_smul]
    module

section uElt_remint
variable {R : Type*} [CommRing R]

def uElt (b : R) : SL(2, R) :=
  ⟨!![1, b; 0, 1], by rw [Matrix.det_fin_two_of]; ring⟩

@[scoped simp] theorem uElt_coe (b : R) : (uElt b : Matrix (Fin 2) (Fin 2) R) = !![1, b; 0, 1] := rfl

theorem uElt_add (b b' : R) : uElt (b + b') = uElt b * uElt b' := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem uElt_pow (b : R) (n : ℕ) : (uElt b) ^ n = uElt ((n : R) * b) := by
  induction n with
  | zero => ext i j; fin_cases i <;> fin_cases j <;> simp
  | succ k ih => rw [_root_.pow_succ, ih, ← uElt_add, Nat.cast_succ, add_mul, one_mul]

end uElt_remint

end Ihara
p2m_reactivate "P2MW.S_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_sq.Ihara"
end Inl_W5_RemintA
p2m_reactivate "P2MW.S_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_sq.Ihara"

section Inl_A3_SL2Surjective

namespace Ihara
p2m_export "Ihara" "ker_eq_bot_of_stem_of_fibre sl2_zmod_sq_congruence_preimage_commute ker_pow_eq_one_of_stem HasTrivialSchurMultiplier"
p2m_open "Ihara"

open Matrix

open scoped MatrixGroups

section ArithmeticLemmas

private lemma natCast_dvd_int {p : ℕ} {z : ℤ} : (p : ℤ) ∣ z ↔ p ∣ z.natAbs :=
  Int.natCast_dvd

private def primeSel (c d : ℤ) : ℕ :=
  ∏ p ∈ c.natAbs.primeFactors, if p ∣ d.natAbs then 1 else p

private lemma dvd_primeSel {c d : ℤ} {p : ℕ} (hc : c ≠ 0) (hp : p.Prime)
    (hpc : (p : ℤ) ∣ c) (hpd : ¬(p : ℤ) ∣ d) : p ∣ primeSel c d := by
  have hmem : p ∈ c.natAbs.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hp, natCast_dvd_int.mp hpc, Int.natAbs_ne_zero.mpr hc⟩
  have h := Finset.dvd_prod_of_mem (fun q : ℕ => if q ∣ d.natAbs then 1 else q) hmem
  simp only [if_neg (fun hcontra => hpd (natCast_dvd_int.mpr hcontra))] at h
  exact h

private lemma not_dvd_primeSel {c d : ℤ} {p : ℕ} (hp : p.Prime) (hpd : (p : ℤ) ∣ d) :
    ¬p ∣ primeSel c d := by
  intro hdvd
  obtain ⟨q, hq, hpq⟩ := (Nat.Prime.prime hp).dvd_finsetProd_iff _ |>.mp hdvd
  by_cases hqd : q ∣ d.natAbs
  · rw [if_pos hqd] at hpq
    exact hp.one_lt.ne' (Nat.dvd_one.mp hpq)
  · rw [if_neg hqd] at hpq
    have hq' : q.Prime := (Nat.mem_primeFactors.mp hq).1
    exact hqd (((Nat.prime_dvd_prime_iff_eq hp hq').mp hpq) ▸ natCast_dvd_int.mp hpd)

theorem exists_coprime_lift (N : ℕ) [NeZero N] {c₀ d₀ : ℤ}
    (H : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ c₀ → (p : ℤ) ∣ d₀ → ¬(p : ℤ) ∣ (N : ℤ)) :
    ∃ γ δ : ℤ, Int.gcd γ δ = 1 ∧
      (γ : ZMod N) = (c₀ : ZMod N) ∧ (δ : ZMod N) = (d₀ : ZMod N) := by

  set γ : ℤ := if c₀ = 0 then (N : ℤ) else c₀ with hγ_def
  have hγ0 : γ ≠ 0 := by
    rw [hγ_def]
    split
    · exact_mod_cast NeZero.ne N
    · assumption
  have hγc : (γ : ZMod N) = (c₀ : ZMod N) := by
    rw [hγ_def]
    split
    · next h => simp [h]
    · rfl
  have Hγ : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ γ → (p : ℤ) ∣ d₀ → ¬(p : ℤ) ∣ (N : ℤ) := by
    intro p pp hpγ hpd
    refine H p pp ?_ hpd
    rw [hγ_def] at hpγ
    by_cases h : c₀ = 0
    · simp [h]
    · rwa [if_neg h] at hpγ

  refine ⟨γ, d₀ + (primeSel γ d₀ : ℤ) * (N : ℤ), ?_, hγc, ?_⟩
  ·
    by_contra hne
    obtain ⟨p, pp, hpdvd⟩ := Nat.exists_prime_and_dvd hne
    have h1 : (p : ℤ) ∣ γ :=
      natCast_dvd_int.mpr (hpdvd.trans (Nat.gcd_dvd_left _ _))
    have h2 : (p : ℤ) ∣ d₀ + (primeSel γ d₀ : ℤ) * (N : ℤ) :=
      natCast_dvd_int.mpr (hpdvd.trans (Nat.gcd_dvd_right _ _))
    by_cases hpd : (p : ℤ) ∣ d₀
    ·
      have h3 : (p : ℤ) ∣ (primeSel γ d₀ : ℤ) * (N : ℤ) := by
        have := h2.sub hpd
        rwa [add_sub_cancel_left] at this
      rcases (Nat.prime_iff_prime_int.mp pp).dvd_or_dvd h3 with h4 | h4
      · exact not_dvd_primeSel pp hpd (natCast_dvd_int.mp h4)
      · exact Hγ p pp h1 hpd h4
    ·
      have h3 : (p : ℤ) ∣ (primeSel γ d₀ : ℤ) :=
        natCast_dvd_int.mpr (dvd_primeSel hγ0 pp h1 hpd)
      refine hpd ?_
      have := h2.sub (h3.mul_right (N : ℤ))
      rwa [add_sub_cancel_right] at this
  ·
    push_cast
    simp

end ArithmeticLemmas
p2m_reactivate "P2MW.S_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_sq.Ihara"

section Lifting

theorem exists_sl2_int_lift {N : ℕ} [NeZero N] {a b c d : ZMod N}
    (h : a * d - b * c = 1) :
    ∃ α β γ δ : ℤ, α * δ - β * γ = 1 ∧
      (α : ZMod N) = a ∧ (β : ZMod N) = b ∧ (γ : ZMod N) = c ∧ (δ : ZMod N) = d := by

  set a₀ : ℤ := ZMod.cast a with ha₀
  set b₀ : ℤ := ZMod.cast b with hb₀
  set c₀ : ℤ := ZMod.cast c with hc₀
  set d₀ : ℤ := ZMod.cast d with hd₀
  have hcasta : ((a₀ : ℤ) : ZMod N) = a := ZMod.intCast_zmod_cast a
  have hcastb : ((b₀ : ℤ) : ZMod N) = b := ZMod.intCast_zmod_cast b
  have hcastc : ((c₀ : ℤ) : ZMod N) = c := ZMod.intCast_zmod_cast c
  have hcastd : ((d₀ : ℤ) : ZMod N) = d := ZMod.intCast_zmod_cast d

  have hdvd : (N : ℤ) ∣ a₀ * d₀ - b₀ * c₀ - 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hcasta, hcastb, hcastc, hcastd]
    rw [sub_eq_zero]
    exact h

  have H : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ c₀ → (p : ℤ) ∣ d₀ → ¬(p : ℤ) ∣ (N : ℤ) := by
    intro p pp hpc hpd hpN
    have hone : (p : ℤ) ∣ 1 := by
      have h1 : (p : ℤ) ∣ a₀ * d₀ - b₀ * c₀ - 1 := hpN.trans hdvd
      have h2 : (p : ℤ) ∣ a₀ * d₀ := hpd.mul_left a₀
      have h3 : (p : ℤ) ∣ b₀ * c₀ := hpc.mul_left b₀
      have key : (1 : ℤ) = a₀ * d₀ - b₀ * c₀ - (a₀ * d₀ - b₀ * c₀ - 1) := by ring
      rw [key]
      exact (h2.sub h3).sub h1
    exact pp.one_lt.ne' (Nat.dvd_one.mp (by exact_mod_cast hone))

  obtain ⟨γ, δ, hγδ, hγ, hδ⟩ := exists_coprime_lift N H
  rw [hcastc] at hγ
  rw [hcastd] at hδ

  set α₀ : ℤ := Int.gcdB γ δ with hα₀
  set β₀ : ℤ := -Int.gcdA γ δ with hβ₀
  have hdet₀ : α₀ * δ - β₀ * γ = 1 := by
    have hbez := Int.gcd_eq_gcd_ab γ δ
    rw [hγδ] at hbez
    push_cast at hbez
    rw [hα₀, hβ₀]
    linear_combination -hbez

  have hdet₀' : (α₀ : ZMod N) * d - (β₀ : ZMod N) * c = 1 := by
    have := congrArg (fun z : ℤ => (z : ZMod N)) hdet₀
    push_cast at this
    rwa [hγ, hδ] at this

  set lam : ZMod N := b * (α₀ : ZMod N) - a * (β₀ : ZMod N) with hlam
  set l : ℤ := ZMod.cast lam with hl
  have hcastl : ((l : ℤ) : ZMod N) = lam := ZMod.intCast_zmod_cast lam
  refine ⟨α₀ + l * γ, β₀ + l * δ, γ, δ, ?_, ?_, ?_, hγ, hδ⟩
  · linear_combination hdet₀
  ·
    push_cast
    rw [hcastl, hγ, hlam]
    linear_combination (-(α₀ : ZMod N)) * h + a * hdet₀'
  ·
    push_cast
    rw [hcastl, hδ, hlam]
    linear_combination (-(β₀ : ZMod N)) * h + b * hdet₀'

theorem SL2_reduction_surjective (N : ℕ) [NeZero N] :
    Function.Surjective
      (SpecialLinearGroup.map (n := Fin 2) (Int.castRingHom (ZMod N))) := by
  intro M
  have hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
    have hM := M.prop
    rwa [Matrix.det_fin_two] at hM
  obtain ⟨α, β, γ, δ, h1, ha, hb, hc, hd⟩ := exists_sl2_int_lift hdet
  refine ⟨⟨!![α, β; γ, δ], by rw [Matrix.det_fin_two_of]; exact h1⟩, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simpa [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
      using ‹_›

end Lifting
p2m_reactivate "P2MW.S_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_sq.Ihara"

end Ihara
p2m_reactivate "P2MW.S_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_sq.Ihara"

end Inl_A3_SL2Surjective
p2m_reactivate "P2MW.S_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_sq.Ihara"

section Inl_P2B_BinomialTwin

set_option autoImplicit false

namespace Ihara
p2m_export "Ihara" "ker_eq_bot_of_stem_of_fibre sl2_zmod_sq_congruence_preimage_commute ker_pow_eq_one_of_stem HasTrivialSchurMultiplier"
p2m_open "Ihara"

section ThreeTermBinomial

variable {R : Type*} [CommRing R]

theorem one_add_smul_pow_three (n : ℕ) (c : R) (A : Matrix (Fin 2) (Fin 2) R) :
    ∃ B : Matrix (Fin 2) (Fin 2) R, (1 + c • A) ^ n =
      1 + ((n : R) * c) • A + (((n.choose 2 : ℕ) : R) * c ^ 2) • (A * A) + c ^ 3 • B := by
  induction n with
  | zero =>
    refine ⟨0, ?_⟩
    simp [Nat.choose_eq_zero_of_lt (show 0 < 2 from Nat.zero_lt_two)]
  | succ l ih =>
    obtain ⟨B, hB⟩ := ih
    refine ⟨((l.choose 2 : ℕ) : R) • (A * A * A) + B + c • (B * A), ?_⟩
    have hc2 : (l + 1).choose 2 = l.choose 2 + l := by
      have := Nat.choose_succ_succ' l 1
      simpa [Nat.choose_one_right, add_comm] using this
    rw [pow_succ, hB, hc2]
    simp only [Nat.cast_add, Nat.cast_succ, add_mul, mul_add, one_mul, mul_one, smul_mul_assoc,
      mul_smul_comm, smul_add, smul_smul]
    module

end ThreeTermBinomial
p2m_reactivate "P2MW.S_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_sq.Ihara"

theorem one_add_smul_pow_eq_of_odd (q m : ℕ) (hq : Odd q) (hm : 3 ≤ m)
    (A : Matrix (Fin 2) (Fin 2) (ZMod (q ^ m))) :
    (1 + ((q : ZMod (q ^ m)) ^ (m - 2)) • A) ^ q
      = 1 + ((q : ZMod (q ^ m)) ^ (m - 1)) • A := by
  obtain ⟨B, hB⟩ := one_add_smul_pow_three q ((q : ZMod (q ^ m)) ^ (m - 2)) A

  have hqm : (q : ZMod (q ^ m)) ^ m = 0 := by rw [← Nat.cast_pow, ZMod.natCast_self]
  have hvan : ∀ k : ℕ, m ≤ k → (q : ZMod (q ^ m)) ^ k = 0 := fun k hk => by
    rw [show k = m + (k - m) by omega, pow_add, hqm, zero_mul]
  have h1 : (q : ZMod (q ^ m)) * (q : ZMod (q ^ m)) ^ (m - 2) = (q : ZMod (q ^ m)) ^ (m - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have h2 : ((q.choose 2 : ℕ) : ZMod (q ^ m)) * ((q : ZMod (q ^ m)) ^ (m - 2)) ^ 2 = 0 := by
    obtain ⟨k, hk⟩ := hq
    have hc : q.choose 2 = q * k := by
      rw [Nat.choose_two_right, hk, show 2 * k + 1 - 1 = 2 * k by omega,
        show (2 * k + 1) * (2 * k) = 2 * ((2 * k + 1) * k) by ring,
        Nat.mul_div_cancel_left _ Nat.zero_lt_two]
    rw [hc, Nat.cast_mul, mul_comm ((q : ℕ) : ZMod (q ^ m)) ((k : ℕ) : ZMod (q ^ m)), mul_assoc,
      ← pow_mul, ← pow_succ', hvan _ (by omega), mul_zero]
  have h3 : ((q : ZMod (q ^ m)) ^ (m - 2)) ^ 3 = 0 := by
    rw [← pow_mul]
    exact hvan _ (by omega)
  rw [hB, h1, h2, h3]
  simp only [zero_smul, add_zero]

theorem one_add_smul_pow_prime_eq (q m : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (hm : 3 ≤ m)
    (A : Matrix (Fin 2) (Fin 2) (ZMod (q ^ m))) :
    (1 + ((q : ZMod (q ^ m)) ^ (m - 2)) • A) ^ q
      = 1 + ((q : ZMod (q ^ m)) ^ (m - 1)) • A :=
  one_add_smul_pow_eq_of_odd q m (hq.odd_of_ne_two hq2) hm A

end Ihara
p2m_reactivate "P2MW.S_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_sq.Ihara"

end Inl_P2B_BinomialTwin
p2m_reactivate "P2MW.S_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_sq.Ihara"

section Inl_P2B_Filtration

set_option autoImplicit false
set_option Elab.async false

namespace Ihara
p2m_export "Ihara" "ker_eq_bot_of_stem_of_fibre sl2_zmod_sq_congruence_preimage_commute ker_pow_eq_one_of_stem HasTrivialSchurMultiplier"
p2m_open "Ihara"

open Matrix
open scoped MatrixGroups

noncomputable section

variable (q m : ℕ)

section sl2coe
variable {R : Type*} [CommRing R]
private theorem sl2coe_mul (A B : SL(2, R)) :
    ((A * B : SL(2, R)) : Matrix (Fin 2) (Fin 2) R)
      = (A : Matrix (Fin 2) (Fin 2) R) * B := rfl
private theorem sl2coe_one :
    ((1 : SL(2, R)) : Matrix (Fin 2) (Fin 2) R) = 1 := rfl
private theorem sl2coe_pow (A : SL(2, R)) (n : ℕ) :
    ((A ^ n : SL(2, R)) : Matrix (Fin 2) (Fin 2) R)
      = (A : Matrix (Fin 2) (Fin 2) R) ^ n := rfl
end sl2coe
p2m_reactivate "P2MW.S_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_sq.Ihara"

def congFilt (a : ℕ) : Subgroup SL(2, ZMod (q ^ m)) where
  carrier := {g | ∃ A : Matrix (Fin 2) (Fin 2) (ZMod (q ^ m)),
    (g : Matrix (Fin 2) (Fin 2) (ZMod (q ^ m))) = 1 + ((q : ZMod (q ^ m)) ^ a) • A}
  one_mem' := ⟨0, by simp⟩
  mul_mem' := by
    rintro x y ⟨A, hA⟩ ⟨B, hB⟩
    refine ⟨A + B + ((q : ZMod (q ^ m)) ^ a) • (A * B), ?_⟩
    rw [sl2coe_mul]
    rw [hA, hB]
    simp only [add_mul, mul_add, one_mul, mul_one, smul_add, smul_mul_assoc,
      mul_smul_comm, smul_smul]
    abel
  inv_mem' := by
    rintro x ⟨A, hA⟩

    refine ⟨-(A * ((x⁻¹ : SL(2, ZMod (q ^ m))) : Matrix (Fin 2) (Fin 2) (ZMod (q ^ m)))),
      ?_⟩
    have h1 : (1 + ((q : ZMod (q ^ m)) ^ a) • A)
        * ((x⁻¹ : SL(2, ZMod (q ^ m))) : Matrix (Fin 2) (Fin 2) (ZMod (q ^ m))) = 1 := by
      rw [← hA, ← sl2coe_mul, mul_inv_cancel,
        sl2coe_one]
    rw [add_mul, one_mul, smul_mul_assoc] at h1
    rw [smul_neg, ← sub_eq_add_neg, eq_sub_iff_add_eq]
    exact h1

theorem mem_congFilt_iff {a : ℕ} {g : SL(2, ZMod (q ^ m))} :
    g ∈ congFilt q m a ↔ ∃ A : Matrix (Fin 2) (Fin 2) (ZMod (q ^ m)),
      (g : Matrix (Fin 2) (Fin 2) (ZMod (q ^ m))) = 1 + ((q : ZMod (q ^ m)) ^ a) • A :=
  Iff.rfl

scoped instance congFilt_normal (a : ℕ) : (congFilt q m a).Normal where
  conj_mem := by
    rintro g ⟨A, hA⟩ x
    refine ⟨(x : Matrix (Fin 2) (Fin 2) (ZMod (q ^ m))) * A
      * ((x⁻¹ : SL(2, ZMod (q ^ m))) : Matrix (Fin 2) (Fin 2) (ZMod (q ^ m))), ?_⟩
    rw [sl2coe_mul, sl2coe_mul]
    rw [hA, mul_add, mul_one, add_mul, mul_smul_comm, smul_mul_assoc]
    rw [← sl2coe_mul, mul_inv_cancel, sl2coe_one]

@[scoped simp] theorem congFilt_zero : congFilt q m 0 = ⊤ := by
  ext g; simp only [mem_congFilt_iff, pow_zero, one_smul, Subgroup.mem_top, iff_true]
  exact ⟨(g : Matrix (Fin 2) (Fin 2) (ZMod (q ^ m))) - 1, by rw [add_sub_cancel]⟩

theorem congFilt_of_self_le {a : ℕ} (ha : m ≤ a) : congFilt q m a = ⊥ := by
  ext g
  simp only [mem_congFilt_iff, Subgroup.mem_bot]
  constructor
  · rintro ⟨A, hA⟩
    have hq0 : ((q : ZMod (q ^ m)) ^ a) = 0 := by
      have h1 : ((q : ZMod (q ^ m)) ^ m) = 0 := by
        have : ((q ^ m : ℕ) : ZMod (q ^ m)) = 0 := ZMod.natCast_self (q ^ m)
        rwa [Nat.cast_pow] at this
      calc ((q : ZMod (q ^ m)) ^ a) = (q : ZMod (q ^ m)) ^ m * (q : ZMod (q ^ m)) ^ (a - m) := by
            rw [← pow_add, Nat.add_sub_cancel' ha]
        _ = 0 := by rw [h1, zero_mul]
    rw [hq0, zero_smul, add_zero] at hA
    ext i j
    rw [show ((1 : SL(2, ZMod (q^m))) : Matrix _ _ _) i j
        = (1 : Matrix (Fin 2) (Fin 2) (ZMod (q^m))) i j from rfl, ← hA]
  · rintro rfl; exact ⟨0, by simp⟩

theorem congFilt_antitone {a b : ℕ} (hab : a ≤ b) : congFilt q m b ≤ congFilt q m a := by
  rintro g ⟨A, hA⟩
  exact ⟨((q : ZMod (q ^ m)) ^ (b - a)) • A, by
    rw [hA, smul_smul, ← pow_add, Nat.add_sub_cancel' hab]⟩

def slReduceLevel (a : ℕ) (ha : a ≤ m) :
    SL(2, ZMod (q ^ m)) →* SL(2, ZMod (q ^ a)) :=
  SpecialLinearGroup.map (ZMod.castHom (pow_dvd_pow q ha) (ZMod (q ^ a)))

theorem congFilt_eq_ker_reduceLevel {a : ℕ} (ha : a ≤ m) [NeZero q] :
    congFilt q m a = (slReduceLevel q m a ha).ker := by
  haveI : NeZero (q ^ m) := ⟨pow_ne_zero m (NeZero.ne q)⟩
  have hqa0 : ((q : ZMod (q ^ a)) ^ a) = 0 := by
    rw [← Nat.cast_pow]; exact ZMod.natCast_self (q ^ a)
  ext g
  constructor
  · rintro ⟨A, hA⟩
    rw [MonoidHom.mem_ker]
    ext i j
    have hcoe : ((slReduceLevel q m a ha g : SL(2, ZMod (q^a)))
        : Matrix (Fin 2) (Fin 2) (ZMod (q^a))) i j
        = ZMod.castHom (pow_dvd_pow q ha) (ZMod (q^a))
            ((g : Matrix (Fin 2) (Fin 2) (ZMod (q^m))) i j) := by
      simp only [slReduceLevel, SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
        Matrix.map_apply]
    rw [hcoe, hA, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul,
      map_pow, map_natCast, hqa0, zero_mul, add_zero,
      show ((1 : SL(2, ZMod (q^a))) : Matrix _ _ _) i j
        = (1 : Matrix (Fin 2) (Fin 2) (ZMod (q^a))) i j from rfl]
    simp only [Matrix.one_apply, apply_ite (ZMod.castHom (pow_dvd_pow q ha) (ZMod (q^a))),
      map_one, map_zero]
  · intro hker

    rw [MonoidHom.mem_ker] at hker
    have hentry : ∀ i j, (q : ZMod (q ^ m)) ^ a ∣
        ((g : Matrix (Fin 2) (Fin 2) (ZMod (q ^ m))) i j
          - (1 : Matrix (Fin 2) (Fin 2) (ZMod (q ^ m))) i j) := by
      intro i j
      set x := (g : Matrix (Fin 2) (Fin 2) (ZMod (q ^ m))) i j
          - (1 : Matrix (Fin 2) (Fin 2) (ZMod (q ^ m))) i j with hxdef
      have hcast : ZMod.castHom (pow_dvd_pow q ha) (ZMod (q ^ a)) x = 0 := by
        have h1 : ZMod.castHom (pow_dvd_pow q ha) (ZMod (q^a))
            ((g : Matrix (Fin 2) (Fin 2) (ZMod (q^m))) i j)
            = (1 : Matrix (Fin 2) (Fin 2) (ZMod (q^a))) i j := by
          have h0 : ((slReduceLevel q m a ha g : SL(2, ZMod (q^a)))
              : Matrix (Fin 2) (Fin 2) (ZMod (q^a))) i j
              = ((1 : SL(2, ZMod (q^a))) : Matrix _ _ _) i j := by rw [hker]
          simpa only [slReduceLevel, SpecialLinearGroup.map_apply_coe,
            RingHom.mapMatrix_apply, Matrix.map_apply, sl2coe_one] using h0
        rw [hxdef, map_sub, h1]
        simp only [Matrix.one_apply,
          apply_ite (ZMod.castHom (pow_dvd_pow q ha) (ZMod (q^a))), map_one, map_zero,
          sub_self]

      have hrepr : ((x.val : ℕ) : ZMod (q ^ m)) = x := by
        rw [ZMod.natCast_val, ZMod.cast_id]
      rw [← hrepr, map_natCast, ZMod.natCast_eq_zero_iff] at hcast
      obtain ⟨y, hy⟩ := hcast
      exact ⟨(y : ZMod (q ^ m)), by rw [← hrepr, hy, Nat.cast_mul, Nat.cast_pow]⟩
    choose Y hY using hentry
    refine ⟨Matrix.of Y, ?_⟩
    ext i j
    rw [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, ← hY,
      add_sub_cancel]

theorem commutator_mem_congFilt_add {a b : ℕ}
    {g h : SL(2, ZMod (q ^ m))} (hg : g ∈ congFilt q m a) (hh : h ∈ congFilt q m b) :
    g * h * g⁻¹ * h⁻¹ ∈ congFilt q m (a + b) := by
  obtain ⟨A, hA⟩ := (mem_congFilt_iff q m).mp hg
  obtain ⟨B, hB⟩ := (mem_congFilt_iff q m).mp hh
  obtain ⟨A', hA'⟩ := (mem_congFilt_iff q m).mp ((congFilt q m a).inv_mem hg)
  obtain ⟨B', hB'⟩ := (mem_congFilt_iff q m).mp ((congFilt q m b).inv_mem hh)
  set x := (q : ZMod (q ^ m)) ^ a with hx
  set y := (q : ZMod (q ^ m)) ^ b with hy

  refine ⟨(A * B - B * A) * (1 + x • A') * (1 + y • B'), ?_⟩
  have hxinv : (1 + x • A) * (1 + x • A') = 1 := by
    rw [← hA, ← hA', ← sl2coe_mul, mul_inv_cancel,
      sl2coe_one]
  have hyinv : (1 + y • B) * (1 + y • B') = 1 := by
    rw [← hB, ← hB', ← sl2coe_mul, mul_inv_cancel,
      sl2coe_one]
  have hcomm : (1 + x • A) * (1 + y • B) - (1 + y • B) * (1 + x • A)
      = (x * y) • (A * B - B * A) := by
    simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm]
    module
  have hcomm' : (1 + x • A) * (1 + y • B)
      = (1 + y • B) * (1 + x • A) + (x * y) • (A * B - B * A) :=
    sub_eq_iff_eq_add'.mp hcomm
  calc ((g * h * g⁻¹ * h⁻¹ : SL(2, ZMod (q ^ m))) : Matrix (Fin 2) (Fin 2) (ZMod (q ^ m)))
      = ((1 + x • A) * (1 + y • B)) * ((1 + x • A') * (1 + y • B')) := by
        simp only [sl2coe_mul, hA, hB, hA', hB', mul_assoc]
    _ = ((1 + y • B) * (1 + x • A) + (x * y) • (A * B - B * A))
          * ((1 + x • A') * (1 + y • B')) := by rw [hcomm']
    _ = (1 + y • B) * ((1 + x • A) * (1 + x • A')) * (1 + y • B')
          + (x * y) • ((A * B - B * A) * ((1 + x • A') * (1 + y • B'))) := by
        rw [add_mul, smul_mul_assoc, mul_assoc, mul_assoc, ← mul_assoc (1 + x • A)]
    _ = 1 + ((q : ZMod (q ^ m)) ^ (a + b))
          • ((A * B - B * A) * (1 + x • A') * (1 + y • B')) := by
        rw [hxinv, mul_one, hyinv, hx, hy, ← pow_add, mul_assoc]

theorem congFilt_commutator_le (a b : ℕ) :
    ⁅congFilt q m a, congFilt q m b⁆ ≤ congFilt q m (a + b) := by
  rw [Subgroup.commutator_le]
  intro g hg h hh
  exact commutator_mem_congFilt_add q m hg hh

theorem congFilt_commutative {a : ℕ} (ha : m ≤ a + a) :
    ∀ g ∈ congFilt q m a, ∀ h ∈ congFilt q m a, g * h = h * g := by
  intro g hg h hh
  have hc : g * h * g⁻¹ * h⁻¹ ∈ congFilt q m (a + a) :=
    commutator_mem_congFilt_add q m hg hh
  have h1 : g * h * g⁻¹ * h⁻¹ = 1 :=
    Subgroup.mem_bot.mp ((congFilt_of_self_le q m ha).symm ▸ hc)
  have h2 : g * h = g * h * g⁻¹ * h⁻¹ * (h * g) := by group
  rw [h2, h1, one_mul]

theorem pow_q_of_one_add_smul_sub_two (hq : q.Prime) (hq2 : q ≠ 2) (hm : 3 ≤ m)
    (A : Matrix (Fin 2) (Fin 2) (ZMod (q ^ m))) :
    (1 + ((q : ZMod (q ^ m)) ^ (m - 2)) • A) ^ q
      = 1 + ((q : ZMod (q ^ m)) ^ (m - 1)) • A :=
  one_add_smul_pow_prime_eq q m hq hq2 hm A

theorem pow_q_mem_congFilt_add_one {a : ℕ} (ha : 1 ≤ a)
    {g : SL(2, ZMod (q ^ m))} (hg : g ∈ congFilt q m a) :
    g ^ q ∈ congFilt q m (a + 1) := by
  obtain ⟨A, hA⟩ := hg
  obtain ⟨B, hB⟩ := one_add_smul_pow q ((q : ZMod (q ^ m)) ^ a) A
  refine ⟨A + ((q : ZMod (q ^ m)) ^ (a - 1)) • B, ?_⟩
  have hcoe : ((g ^ q : SL(2, ZMod (q ^ m))) : Matrix (Fin 2) (Fin 2) (ZMod (q ^ m)))
      = (1 + ((q : ZMod (q ^ m)) ^ a) • A) ^ q := by
    rw [sl2coe_pow]; rw [hA]
  rw [hcoe, hB, smul_add, smul_smul]
  have h1 : ((q : ℕ) : ZMod (q ^ m)) * (q : ZMod (q ^ m)) ^ a
      = (q : ZMod (q ^ m)) ^ (a + 1) := by rw [← pow_succ']
  have h2 : ((q : ZMod (q ^ m)) ^ a) ^ 2
      = (q : ZMod (q ^ m)) ^ (a + 1) * (q : ZMod (q ^ m)) ^ (a - 1) := by
    rw [← pow_mul, ← pow_add]; congr 1; omega
  rw [h1, h2, add_assoc]

theorem congFilt_pow_q_eq_one {g : SL(2, ZMod (q ^ m))} (hm : 2 ≤ m)
    (hg : g ∈ congFilt q m (m - 1)) : g ^ q = 1 := by
  have h := pow_q_mem_congFilt_add_one q m (a := m - 1) (by omega) hg
  rw [Nat.sub_add_cancel (by omega : 1 ≤ m)] at h
  exact Subgroup.mem_bot.mp ((congFilt_of_self_le q m le_rfl).symm ▸ h)

theorem coe_pow_q_of_mem_congFilt_sub_two (hq : q.Prime) (hq2 : q ≠ 2) (hm : 3 ≤ m)
    {l : SL(2, ZMod (q ^ m))} {X : Matrix (Fin 2) (Fin 2) (ZMod (q ^ m))}
    (hl : (l : Matrix (Fin 2) (Fin 2) (ZMod (q ^ m)))
        = 1 + ((q : ZMod (q ^ m)) ^ (m - 2)) • X) :
    ((l ^ q : SL(2, ZMod (q ^ m))) : Matrix (Fin 2) (Fin 2) (ZMod (q ^ m)))
        = 1 + ((q : ZMod (q ^ m)) ^ (m - 1)) • X := by
  rw [sl2coe_pow]
  rw [hl, pow_q_of_one_add_smul_sub_two q m hq hq2 hm]

theorem zmod_dvd_of_pow_mul_eq_zero (hq : q.Prime) (hm : 1 ≤ m) {x : ZMod (q ^ m)}
    (hx : (q : ZMod (q ^ m)) ^ (m - 1) * x = 0) : (q : ZMod (q ^ m)) ∣ x := by
  haveI : NeZero (q ^ m) := ⟨pow_ne_zero m hq.ne_zero⟩
  have hrepr : ((x.val : ℕ) : ZMod (q ^ m)) = x := by
    rw [ZMod.natCast_val, ZMod.cast_id]
  rw [← hrepr, ← Nat.cast_pow, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff] at hx
  set v := x.val with hv
  have hdvd : q ∣ v := by
    have heq : q ^ m = q ^ (m - 1) * q := by rw [← pow_succ, Nat.sub_add_cancel hm]
    rw [heq] at hx
    exact (Nat.mul_dvd_mul_iff_left (pow_pos hq.pos (m - 1))).mp hx
  obtain ⟨y, hy⟩ := hdvd
  exact ⟨(y : ZMod (q ^ m)), by rw [← hrepr, hy, Nat.cast_mul]⟩

theorem congFilt_pow_q_injOn (hq : q.Prime) (hq2 : q ≠ 2) (hm : 3 ≤ m) :
    ∀ l ∈ congFilt q m (m - 2), l ^ q = 1 → l ∈ congFilt q m (m - 1) := by
  rintro l ⟨X, hX⟩ hlq
  have h := coe_pow_q_of_mem_congFilt_sub_two q m hq hq2 hm hX
  rw [hlq] at h
  rw [sl2coe_one] at h
  rw [eq_comm, add_eq_left] at h

  have hdvd : ∀ i j, (q : ZMod (q ^ m)) ∣ X i j := by
    intro i j
    apply zmod_dvd_of_pow_mul_eq_zero q m hq (by omega)
    have hentry := congrArg (fun M => M i j) h
    simpa only [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply] using hentry
  choose Y hY using hdvd
  refine ⟨Matrix.of Y, ?_⟩
  rw [hX]
  congr 1
  ext i j
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, hY,
    ← mul_assoc, ← pow_succ]
  congr 2
  omega

theorem det_one_add_smul_fin_two {R : Type*} [CommRing R] (c : R)
    (X : Matrix (Fin 2) (Fin 2) R) :
    (1 + c • X).det = 1 + c * Matrix.trace X + c ^ 2 * X.det := by
  rw [Matrix.one_fin_two, Matrix.det_fin_two, Matrix.trace_fin_two, Matrix.det_fin_two]
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Matrix.empty_val']
  ring

theorem congFilt_exists_pow_q (hq : q.Prime) (hq2 : q ≠ 2) (hm : 3 ≤ m) [NeZero q] :
    ∀ k ∈ congFilt q m (m - 1), ∃ l ∈ congFilt q m (m - 2), l ^ q = k := by
  intro k hk
  rw [mem_congFilt_iff] at hk
  obtain ⟨X, hX⟩ := hk
  haveI : NeZero (q ^ m) := ⟨pow_ne_zero m (NeZero.ne q)⟩
  set qm : ZMod (q ^ m) := (q : ZMod (q ^ m)) with hqm
  have hqm_pow_m : qm ^ m = 0 := by
    simp only [hqm, ← Nat.cast_pow, ZMod.natCast_self]
  have hqm_pow_of_le : ∀ {j : ℕ}, m ≤ j → qm ^ j = 0 := fun {j} hj => by
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hj
    rw [hd, pow_add, hqm_pow_m, zero_mul]

  have hdetk := k.det_coe
  rw [hX, det_one_add_smul_fin_two] at hdetk
  have hqm2m2 : (qm ^ (m - 1)) ^ 2 = 0 := by
    rw [← pow_mul]; exact hqm_pow_of_le (by omega)
  rw [hqm2m2, zero_mul, add_zero] at hdetk
  have htr0 : qm ^ (m - 1) * Matrix.trace X = 0 := by linear_combination hdetk

  obtain ⟨t, ht⟩ := zmod_dvd_of_pow_mul_eq_zero q m hq (by omega) htr0

  set a : ZMod (q ^ m) := -t - qm ^ (m - 3) * X.det with ha
  set Y : Matrix (Fin 2) (Fin 2) (ZMod (q ^ m)) := !![a, 0; 0, 0] with hY
  set Z : Matrix (Fin 2) (Fin 2) (ZMod (q ^ m)) := X + qm • Y with hZ

  have hdetl : (1 + qm ^ (m - 2) • Z).det = 1 := by
    rw [det_one_add_smul_fin_two]

    have htrZ : Matrix.trace Z = qm * (t + a) := by
      rw [hZ, Matrix.trace_add, Matrix.trace_smul, hY, Matrix.trace_fin_two_of,
        smul_eq_mul, add_zero, ht, ← hqm]
      ring
    have hdetZ : Z.det = X.det + qm * a * X 1 1 := by
      rw [hZ, Matrix.det_fin_two, Matrix.det_fin_two, hY]
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, Matrix.empty_val', mul_zero, add_zero]
      ring
    rw [htrZ, hdetZ]

    have heq1 : qm ^ (m - 2) * (qm * (t + a)) = qm ^ (m - 1) * (t + a) := by
      rw [show m - 1 = m - 2 + 1 from by omega, pow_succ]; ring
    have heq2 : (qm ^ (m - 2)) ^ 2 = qm ^ (2 * (m - 2)) := by rw [← pow_mul, mul_comm]
    rw [heq1, heq2]

    have hta : t + a = -(qm ^ (m - 3) * X.det) := by rw [ha]; ring
    rw [hta, mul_neg, ← mul_assoc, ← pow_add]
    have hstep : m - 1 + (m - 3) = 2 * (m - 2) := by omega
    rw [hstep, mul_add, ← add_assoc, neg_add_cancel_right]

    rw [show qm ^ (2 * (m - 2)) * (qm * a * X 1 1)
        = qm ^ (2 * (m - 2) + 1) * (a * X 1 1) from by ring,
      hqm_pow_of_le (by omega), zero_mul, add_zero]

  refine ⟨⟨_, hdetl⟩, (mem_congFilt_iff q m).mpr ⟨Z, rfl⟩, ?_⟩

  apply Matrix.SpecialLinearGroup.ext
  intro i j
  have hlq := coe_pow_q_of_mem_congFilt_sub_two q m hq hq2 hm
    (l := ⟨_, hdetl⟩) (X := Z) rfl
  rw [hlq, hX, hZ, smul_add, smul_smul, ← pow_succ,
    show m - 1 + 1 = m from by omega, hqm_pow_m, zero_smul, add_zero]

theorem slReduceLevel_surjective [NeZero q] {a : ℕ} (ha : a ≤ m) :
    Function.Surjective (slReduceLevel q m a ha) := by
  intro g
  haveI : NeZero (q ^ a) := ⟨pow_ne_zero a (NeZero.ne q)⟩
  haveI : NeZero (q ^ m) := ⟨pow_ne_zero m (NeZero.ne q)⟩

  obtain ⟨g', hg'⟩ := SL2_reduction_surjective (q ^ a) g
  refine ⟨SpecialLinearGroup.map (Int.castRingHom (ZMod (q ^ m))) g', ?_⟩
  rw [← hg']
  ext i j
  simp only [slReduceLevel, SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
    Matrix.map_apply]
  exact map_intCast _ _

noncomputable def congFiltQuotientEquiv (hm : 1 ≤ m) [NeZero q] :
    SL(2, ZMod (q ^ m)) ⧸ congFilt q m (m - 1) ≃* SL(2, ZMod (q ^ (m - 1))) :=
  (QuotientGroup.quotientMulEquivOfEq
    (congFilt_eq_ker_reduceLevel q m (a := m - 1) (by omega))).trans
  (QuotientGroup.quotientKerEquivOfSurjective _
    (slReduceLevel_surjective q m (by omega)))

end
p2m_reactivate "P2MW.S_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_sq.Ihara"

end Ihara
p2m_reactivate "P2MW.S_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_sq.Ihara"

end Inl_P2B_Filtration
p2m_reactivate "P2MW.S_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_sq.Ihara"

section Inl_P2A_SL2Card

namespace Ihara
p2m_export "Ihara" "ker_eq_bot_of_stem_of_fibre sl2_zmod_sq_congruence_preimage_commute ker_pow_eq_one_of_stem HasTrivialSchurMultiplier"
p2m_open "Ihara"

open Matrix

open scoped MatrixGroups

variable (F : Type*) [Field F]

private lemma det_GL_two_surjective :
    Function.Surjective (GeneralLinearGroup.det : GL (Fin 2) F →* Fˣ) := by
  intro u
  have hmul : ∀ x y : F, !![x, 0; 0, 1] * !![y, 0; 0, 1] = !![x * y, 0; 0, 1] := by
    intro x y
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hone : (1 : Matrix (Fin 2) (Fin 2) F) = !![1, 0; 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  refine ⟨⟨!![(u : F), 0; 0, 1], !![((u⁻¹ : Fˣ) : F), 0; 0, 1], ?_, ?_⟩, ?_⟩
  · rw [hmul, hone]
    norm_num
  · rw [hmul, hone]
    norm_num
  · apply Units.ext
    rw [GeneralLinearGroup.val_det_apply]
    show Matrix.det !![(u : F), 0; 0, 1] = (u : F)
    rw [Matrix.det_fin_two_of]
    ring

private lemma card_ker_det_GL_two :
    Nat.card (MonoidHom.ker (GeneralLinearGroup.det : GL (Fin 2) F →* Fˣ)) =
      Nat.card (SpecialLinearGroup (Fin 2) F) := by
  refine (Nat.card_eq_of_bijective
    (fun g : SpecialLinearGroup (Fin 2) F =>
      (⟨SpecialLinearGroup.toGL g, by
        rw [MonoidHom.mem_ker]
        exact SpecialLinearGroup.coeToGL_det g⟩ :
        MonoidHom.ker (GeneralLinearGroup.det : GL (Fin 2) F →* Fˣ)))
    ⟨?_, ?_⟩).symm
  · intro g g' hgg'
    exact SpecialLinearGroup.toGL_injective (Subtype.ext_iff.mp hgg')
  · rintro ⟨A, hA⟩
    rw [MonoidHom.mem_ker] at hA
    have hAdet : (A : Matrix (Fin 2) (Fin 2) F).det = 1 := by
      have := congrArg (Units.val) hA
      rwa [GeneralLinearGroup.val_det_apply, Units.val_one] at this
    refine ⟨⟨(A : Matrix (Fin 2) (Fin 2) F), hAdet⟩, ?_⟩
    apply Subtype.ext
    apply Units.ext
    rfl

theorem card_SL2_zmod (p : ℕ) [Fact p.Prime] :
    Nat.card (SpecialLinearGroup (Fin 2) (ZMod p)) = p * (p ^ 2 - 1) := by
  have hp : p.Prime := Fact.out
  have key : Nat.card (GL (Fin 2) (ZMod p)) =
      (p - 1) * Nat.card (SpecialLinearGroup (Fin 2) (ZMod p)) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
      (MonoidHom.ker (GeneralLinearGroup.det : GL (Fin 2) (ZMod p) →* (ZMod p)ˣ))]
    rw [card_ker_det_GL_two]
    congr 1
    rw [Nat.card_congr
      (QuotientGroup.quotientKerEquivOfSurjective _ (det_GL_two_surjective (ZMod p))).toEquiv]
    rw [Nat.card_eq_fintype_card, ZMod.card_units]
  rw [Matrix.card_GL_field, ZMod.card, Fin.prod_univ_two] at key
  norm_num at key
  have h1 : 1 ≤ p := hp.one_lt.le
  have h2 : p ≤ p ^ 2 := by nlinarith
  have h3 : 1 ≤ p ^ 2 := h1.trans h2
  have harith : (p ^ 2 - 1) * (p ^ 2 - p) = (p - 1) * (p * (p ^ 2 - 1)) := by
    zify [h1, h2, h3]
    ring
  rw [harith] at key
  rw [Nat.card_eq_fintype_card]
  exact Nat.eq_of_mul_eq_mul_left (Nat.sub_pos_of_lt hp.one_lt) key.symm

end Ihara
p2m_reactivate "P2MW.S_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_sq.Ihara"

end Inl_P2A_SL2Card
p2m_reactivate "P2MW.S_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_sq.Ihara"

section Inl_W5_RemintB

namespace Ihara
p2m_export "Ihara" "ker_eq_bot_of_stem_of_fibre sl2_zmod_sq_congruence_preimage_commute ker_pow_eq_one_of_stem HasTrivialSchurMultiplier"
p2m_open "Ihara"

open Matrix
open scoped MatrixGroups

section unipU_remint
variable (q : ℕ)

def unipU : SL(2, ZMod q) :=
  ⟨!![1, 1; 0, 1], by rw [Matrix.det_fin_two_of]; ring⟩

theorem unipU_pow_coe (n : ℕ) :
    ((unipU q ^ n : SL(2, ZMod q)) : Matrix (Fin 2) (Fin 2) (ZMod q))
      = !![1, (n : ZMod q); 0, 1] := by
  induction n with
  | zero => rw [pow_zero, Nat.cast_zero]; exact Matrix.one_fin_two
  | succ n ih =>
    rw [_root_.pow_succ]
    change ((unipU q ^ n : SL(2, ZMod q)) : Matrix (Fin 2) (Fin 2) (ZMod q))
      * !![1, 1; 0, 1] = _
    rw [ih, Matrix.mul_fin_two, Nat.cast_succ]; simp [add_comm]

theorem unipU_pow_self [Fact q.Prime] : unipU q ^ q = 1 :=
  Subtype.ext <| by rw [unipU_pow_coe, ZMod.natCast_self]; exact Matrix.one_fin_two.symm

theorem unipU_ne_one [Fact q.Prime] : unipU q ≠ 1 := by
  intro h
  have h01 := congrArg (fun g : SL(2, ZMod q) => (g : Matrix (Fin 2) (Fin 2) (ZMod q)) 0 1) h
  change (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) (ZMod q)) 0 1
    = (1 : Matrix (Fin 2) (Fin 2) (ZMod q)) 0 1 at h01
  simp at h01

theorem orderOf_unipU [Fact q.Prime] : orderOf (unipU q) = q :=
  orderOf_eq_prime (unipU_pow_self q) (unipU_ne_one q)

theorem index_zpowers_unipU [Fact q.Prime] :
    (Subgroup.zpowers (unipU q)).index = q ^ 2 - 1 := by
  have hq : 0 < q := (Fact.out : q.Prime).pos
  have h := (Subgroup.zpowers (unipU q)).card_mul_index
  rw [Nat.card_zpowers, orderOf_unipU, card_SL2_zmod q] at h
  exact Nat.eq_of_mul_eq_mul_left hq h

end unipU_remint
p2m_reactivate "P2MW.S_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_sq.Ihara"

variable (q : ℕ) {E : Type} [Group E]

theorem comap_congFilt_one_commute (π : E →* SL(2, ZMod (q ^ 2)))
    (hsurj : Function.Surjective π) (hcen : MonoidHom.ker π ≤ Subgroup.center E)
    (hq : q.Prime) (hq5 : 5 ≤ q) [NeZero q] :
    ∀ x ∈ (congFilt q 2 1).comap π, ∀ y ∈ (congFilt q 2 1).comap π, Commute x y := by
  intro x hx y hy
  refine Ihara.sl2_zmod_sq_congruence_preimage_commute q π hsurj hcen hq hq5 x ?_ y ?_
  · obtain ⟨A, hA⟩ := (mem_congFilt_iff q 2).mp (Subgroup.mem_comap.mp hx)
    exact ⟨A, by rw [pow_one] at hA; exact hA⟩
  · obtain ⟨B, hB⟩ := (mem_congFilt_iff q 2).mp (Subgroup.mem_comap.mp hy)
    exact ⟨B, by rw [pow_one] at hB; exact hB⟩

end Ihara
p2m_reactivate "P2MW.S_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_sq.Ihara"
end Inl_W5_RemintB
p2m_reactivate "P2MW.S_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_sq.Ihara"

section Inl_P2B_M2SchurTrivial

set_option autoImplicit false

p2m_open "Matrix SpecialLinearGroup Matrix.SpecialLinearGroup Subgroup"

open scoped MatrixGroups

namespace Ihara
p2m_export "Ihara" "ker_eq_bot_of_stem_of_fibre sl2_zmod_sq_congruence_preimage_commute ker_pow_eq_one_of_stem HasTrivialSchurMultiplier"
p2m_open "Ihara"

variable (q : ℕ)

private theorem sl2coe_mul'' {R : Type*} [CommRing R] (A B : SL(2, R)) :
    ((A * B : SL(2, R)) : Matrix (Fin 2) (Fin 2) R)
      = (A : Matrix (Fin 2) (Fin 2) R) * B := rfl

abbrev unipU2 : SL(2, ZMod (q ^ 2)) := uElt (R := ZMod (q ^ 2)) 1

theorem slReduceLevel_unipU2 :
    slReduceLevel q 2 1 (by omega) (unipU2 q) = unipU (q ^ 1) := by
  ext i j
  simp only [slReduceLevel, SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
    Matrix.map_apply, unipU2, uElt_coe, unipU]
  fin_cases i <;> fin_cases j <;> simp

theorem congFilt_one_commute_unipU2_mem_zpowers (hq : q.Prime) (hq5 : 5 ≤ q) :
    ∀ k ∈ congFilt q 2 1, unipU2 q * k = k * unipU2 q →
      k ∈ Subgroup.zpowers (unipU2 q) := by
  intro k hk hcomm
  obtain ⟨X, hX⟩ := (mem_congFilt_iff q 2).mp hk
  rw [pow_one] at hX

  have hmat : (q : ZMod (q^2)) •
      (!![(1:ZMod (q^2)),1;0,1] * X - X * !![1,1;0,1]) = 0 := by
    have hcoe := congrArg
      (fun g => ((g : SL(2, ZMod (q^2))) : Matrix (Fin 2) (Fin 2) (ZMod (q^2)))) hcomm
    simp only [sl2coe_mul'', hX,
      show ((unipU2 q : SL(2, ZMod (q^2))) : Matrix _ _ _)
        = !![(1:ZMod (q^2)),1;0,1] from rfl] at hcoe
    rw [mul_add, mul_one, add_mul, one_mul, Matrix.mul_smul, Matrix.smul_mul] at hcoe
    rw [smul_sub, sub_eq_zero]; exact add_left_cancel hcoe

  have hmat' := fun i j => congrFun (congrFun hmat i) j
  have hqX10 : (q : ZMod (q^2)) * X 1 0 = 0 := by
    have h00 := hmat' 0 0
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.sub_apply, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.zero_apply, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Matrix.empty_val'] at h00
    linear_combination h00
  have hqXdd : (q : ZMod (q^2)) * (X 1 1 - X 0 0) = 0 := by
    have h01 := hmat' 0 1
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.sub_apply, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.zero_apply, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Matrix.empty_val'] at h01
    linear_combination h01

  have hq2z : ((q : ZMod (q^2)) ^ 2 : ZMod (q^2)) = 0 := by
    rw [← Nat.cast_pow]; exact ZMod.natCast_self _
  have hdet := k.det_coe
  rw [hX, det_one_add_smul_fin_two, hq2z, zero_mul, add_zero] at hdet
  have hqXtr : (q : ZMod (q^2)) * (X 0 0 + X 1 1) = 0 := by
    rw [← Matrix.trace_fin_two]; linear_combination hdet

  have h2u : IsUnit (2 : ZMod (q^2)) :=
    (ZMod.isUnit_iff_coprime 2 (q^2)).mpr
      ((Nat.coprime_primes Nat.prime_two hq).mpr (by omega) |>.pow_right 2)
  have hqX00 : (q : ZMod (q^2)) * X 0 0 = 0 := by
    have h2 : 2 * ((q : ZMod (q^2)) * X 0 0) = 0 := by linear_combination hqXtr - hqXdd
    exact h2u.mul_right_eq_zero.mp h2
  have hqX11 : (q : ZMod (q^2)) * X 1 1 = 0 := by
    have h2 : 2 * ((q : ZMod (q^2)) * X 1 1) = 0 := by linear_combination hqXtr + hqXdd
    exact h2u.mul_right_eq_zero.mp h2

  haveI : NeZero (q ^ 2) := ⟨pow_ne_zero 2 hq.ne_zero⟩
  have hval : (((((q : ZMod (q^2)) * X 0 1).val : ℕ) : ZMod (q^2)))
      = (q : ZMod (q^2)) * X 0 1 := by
    rw [ZMod.natCast_val, ZMod.cast_id]
  refine Subgroup.mem_zpowers_iff.mpr
    ⟨(((q : ZMod (q^2)) * X 0 1).val : ℤ), ?_⟩
  rw [zpow_natCast, unipU2, uElt_pow (1 : ZMod (q^2)), mul_one, hval]
  apply Matrix.SpecialLinearGroup.ext; intro i j
  rw [hX, uElt_coe, Matrix.one_fin_two]
  fin_cases i <;> fin_cases j <;> simp [hqX00, hqX10, hqX11]

theorem hasTrivialSchurMultiplier_SL2_ZMod_sq_impl (hq : q.Prime) (hq5 : 5 ≤ q)
    (hperf : commutator SL(2, ZMod (q ^ 2)) = ⊤)
    (IH : HasTrivialSchurMultiplier SL(2, ZMod (q ^ 1))) :
    HasTrivialSchurMultiplier SL(2, ZMod (q ^ 2)) := by
  haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI : Fact q.Prime := ⟨hq⟩
  intro E _ π hπ hcen hC
  have hQ : HasTrivialSchurMultiplier (SL(2, ZMod (q ^ 2)) ⧸ congFilt q 2 1) :=
    IH.of_mulEquiv (congFiltQuotientEquiv q 2 (by omega))
  have hK : congFilt q 2 1 ≤ commutator SL(2, ZMod (q ^ 2)) := by
    rw [hperf]; exact le_top
  have hCq : ∀ c ∈ π.ker, c ^ q = 1 :=
    ker_pow_eq_one_of_stem π hπ hcen hC (congFilt q 2 1) hK hQ
      (congFilt_commutative q 2 (a := 1) (by omega)) (hq.odd_of_ne_two (by omega))
      (fun _ hk => congFilt_pow_q_eq_one q 2 (by omega) hk)

  haveI : Fact (q ^ 1).Prime := ⟨by rw [pow_one]; exact hq⟩
  have hρu : slReduceLevel q 2 1 (by omega) (unipU2 q) = unipU (q^1) := slReduceLevel_unipU2 q
  have hidx : Nat.Coprime
      ((Subgroup.zpowers (slReduceLevel q 2 1 (by omega) (unipU2 q))).comap
        (slReduceLevel q 2 1 (by omega))).index q := by
    rw [Subgroup.index_comap_of_surjective _
        (slReduceLevel_surjective q 2 (a := 1) (by omega)),
      hρu, index_zpowers_unipU (q ^ 1),
      show (q ^ 1) ^ 2 - 1 = q ^ 2 - 1 from by rw [pow_one]]
    have h1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq.pos
    exact ((Nat.coprime_pow_left_iff two_pos q (q ^ 2 - 1)).mp
      ((Nat.coprime_self_sub_right h1).mpr (Nat.coprime_one_right _))).symm

  exact ker_eq_bot_of_stem_of_fibre π hπ hcen hC (congFilt q 2 1)
    (fun x hx y hy => comap_congFilt_one_commute q π hπ hcen hq hq5 x hx y hy)
    hCq (slReduceLevel q 2 1 (by omega))
    (congFilt_eq_ker_reduceLevel (q := q) (m := 2) (a := 1) (by omega)).symm
    (unipU2 q) hidx
    (congFilt_one_commute_unipU2_mem_zpowers q hq hq5)

end Ihara
p2m_reactivate "P2MW.S_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_sq.Ihara"

end Inl_P2B_M2SchurTrivial
p2m_reactivate "P2MW.S_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_sq.Ihara"

open scoped MatrixGroups

theorem solution (q : ℕ) (hq : q.Prime) (hq5 : 5 ≤ q)
    (hperf : commutator SL(2, ZMod (q ^ 2)) = ⊤)
    (IH : Ihara.HasTrivialSchurMultiplier SL(2, ZMod (q ^ 1))) :
    Ihara.HasTrivialSchurMultiplier SL(2, ZMod (q ^ 2)) :=
  Ihara.hasTrivialSchurMultiplier_SL2_ZMod_sq_impl q hq hq5 hperf IH

#print axioms solution

end S_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_sq
end P2MW
export P2MW.S_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_sq (solution)
