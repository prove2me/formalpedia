-- Prove2me | solution 1 for Ihara.sl2_zmod_sq_congruence_preimage_commute
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/80e31a46-5a20-5d81-a5e9-cbf8eb768a69

import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Module
import Mathlib.GroupTheory.QuotientGroup.Basic
import Definitions.Def_SchurMultiplierTrivial
import Mathlib.Tactic.Group
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Tactic.LinearCombination
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Ihara_sl2_zmod_sq_congruence_preimage_commute

section Inl_W3_Remint

namespace Ihara
p2m_open "Ihara"

open Matrix

open scoped MatrixGroups

private theorem sl2coe_mul_rm {R : Type*} [CommRing R] (A B : SL(2, R)) :
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

section Elementary

variable {R : Type*} [CommRing R]

def uElt (b : R) : SL(2, R) :=
  ⟨!![1, b; 0, 1], by rw [Matrix.det_fin_two_of]; ring⟩

def vElt (c : R) : SL(2, R) :=
  ⟨!![1, 0; c, 1], by rw [Matrix.det_fin_two_of]; ring⟩

def hElt (t : Rˣ) : SL(2, R) :=
  ⟨!![((t⁻¹ : Rˣ) : R), 0; 0, (t : R)], by rw [Matrix.det_fin_two_of]; simp⟩

@[scoped simp] theorem uElt_coe (b : R) : (uElt b : Matrix (Fin 2) (Fin 2) R) = !![1, b; 0, 1] := rfl
@[scoped simp] theorem vElt_coe (c : R) : (vElt c : Matrix (Fin 2) (Fin 2) R) = !![1, 0; c, 1] := rfl
@[scoped simp] theorem hElt_coe (t : Rˣ) :
    (hElt t : Matrix (Fin 2) (Fin 2) R) = !![((t⁻¹ : Rˣ) : R), 0; 0, (t : R)] := rfl

theorem uElt_add (b b' : R) : uElt (b + b') = uElt b * uElt b' := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem hElt_mul (s t : Rˣ) : hElt (s * t) = hElt s * hElt t := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

theorem hElt_one : hElt (1 : Rˣ) = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem hElt_inv (t : Rˣ) : (hElt t)⁻¹ = hElt t⁻¹ :=
  inv_eq_of_mul_eq_one_right (by rw [← hElt_mul, mul_inv_cancel, hElt_one])

theorem hElt_inv_mul_uElt_mul_hElt (t : Rˣ) (b : R) :
    (hElt t)⁻¹ * uElt b * hElt t = uElt ((t : R) ^ 2 * b) := by
  have h1 : (t : R) * ((t⁻¹ : Rˣ) : R) = 1 := Units.mul_inv t
  have h2 : ((t⁻¹ : Rˣ) : R) * (t : R) = 1 := Units.inv_mul t
  rw [hElt_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [sl2coe_mul_rm, uElt_coe, hElt_coe, inv_inv,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Fin.isValue, Fin.zero_eta,
      Fin.mk_one]
  · linear_combination h1
  · ring
  · ring
  · linear_combination h2

end Elementary

end Ihara
p2m_reactivate "P2MW.S_Ihara_sl2_zmod_sq_congruence_preimage_commute.Ihara"
end Inl_W3_Remint
p2m_reactivate "P2MW.S_Ihara_sl2_zmod_sq_congruence_preimage_commute.Ihara"

section Inl_A3_SL2Surjective

namespace Ihara
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
p2m_reactivate "P2MW.S_Ihara_sl2_zmod_sq_congruence_preimage_commute.Ihara"

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
p2m_reactivate "P2MW.S_Ihara_sl2_zmod_sq_congruence_preimage_commute.Ihara"

end Ihara
p2m_reactivate "P2MW.S_Ihara_sl2_zmod_sq_congruence_preimage_commute.Ihara"

end Inl_A3_SL2Surjective
p2m_reactivate "P2MW.S_Ihara_sl2_zmod_sq_congruence_preimage_commute.Ihara"

section Inl_P2B_BinomialTwin

set_option autoImplicit false

namespace Ihara
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
p2m_reactivate "P2MW.S_Ihara_sl2_zmod_sq_congruence_preimage_commute.Ihara"

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
p2m_reactivate "P2MW.S_Ihara_sl2_zmod_sq_congruence_preimage_commute.Ihara"

end Inl_P2B_BinomialTwin
p2m_reactivate "P2MW.S_Ihara_sl2_zmod_sq_congruence_preimage_commute.Ihara"

section Inl_P2B_Filtration

set_option autoImplicit false
set_option Elab.async false

namespace Ihara
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
p2m_reactivate "P2MW.S_Ihara_sl2_zmod_sq_congruence_preimage_commute.Ihara"

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
p2m_reactivate "P2MW.S_Ihara_sl2_zmod_sq_congruence_preimage_commute.Ihara"

end Ihara
p2m_reactivate "P2MW.S_Ihara_sl2_zmod_sq_congruence_preimage_commute.Ihara"

end Inl_P2B_Filtration
p2m_reactivate "P2MW.S_Ihara_sl2_zmod_sq_congruence_preimage_commute.Ihara"

section Inl_P2B_M2WAbelian

namespace Ihara
p2m_open "Ihara"

p2m_open "Matrix SpecialLinearGroup Matrix.SpecialLinearGroup"

open scoped MatrixGroups commutatorElement

variable (q : ℕ)

private theorem sl2coe_mul' {R : Type*} [CommRing R] (A B : SL(2, R)) :
    ((A * B : SL(2, R)) : Matrix (Fin 2) (Fin 2) R)
      = (A : Matrix (Fin 2) (Fin 2) R) * B := rfl
private theorem sl2coe_mk' {R : Type*} [CommRing R]
    (A : Matrix (Fin 2) (Fin 2) R) (h : A.det = 1) :
    ((⟨A, h⟩ : SL(2, R)) : Matrix (Fin 2) (Fin 2) R) = A := rfl

section Elements

variable [NeZero q]

abbrev kE : SL(2, ZMod (q ^ 2)) := uElt (q : ZMod (q ^ 2))

abbrev kF : SL(2, ZMod (q ^ 2)) := vElt (q : ZMod (q ^ 2))

def kH : SL(2, ZMod (q ^ 2)) :=
  ⟨!![1 + (q : ZMod (q^2)), 0; 0, 1 - (q : ZMod (q^2))], by
    rw [Matrix.det_fin_two_of]; ring_nf
    rw [show ((q : ZMod (q^2))^2 : ZMod (q^2)) = 0 from by
      rw [← Nat.cast_pow]; exact ZMod.natCast_self (q ^ 2)]; ring⟩

def weyl2 : SL(2, ZMod (q ^ 2)) :=
  ⟨!![0, -1; 1, 0], by rw [Matrix.det_fin_two_of]; ring⟩

omit [NeZero q] in
private theorem q_sq_eq_zero : ((q : ZMod (q ^ 2)) ^ 2 : ZMod (q ^ 2)) = 0 := by
  rw [← Nat.cast_pow]; exact ZMod.natCast_self (q ^ 2)

omit [NeZero q] in
theorem kE_coe : ((kE q : SL(2, ZMod (q^2))) : Matrix (Fin 2) (Fin 2) (ZMod (q^2)))
    = !![1, (q : ZMod (q^2)); 0, 1] := rfl

omit [NeZero q] in
theorem kF_coe : ((kF q : SL(2, ZMod (q^2))) : Matrix (Fin 2) (Fin 2) (ZMod (q^2)))
    = !![1, 0; (q : ZMod (q^2)), 1] := rfl

omit [NeZero q] in
theorem kH_coe : ((kH q : SL(2, ZMod (q^2))) : Matrix (Fin 2) (Fin 2) (ZMod (q^2)))
    = !![1 + (q : ZMod (q^2)), 0; 0, 1 - (q : ZMod (q^2))] := rfl

omit [NeZero q] in
theorem kE_mem : kE q ∈ congFilt q 2 1 :=
  (mem_congFilt_iff q 2).mpr ⟨!![0, 1; 0, 0], by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [kE, uElt, pow_one, Matrix.one_fin_two]⟩

omit [NeZero q] in
theorem kF_mem : kF q ∈ congFilt q 2 1 :=
  (mem_congFilt_iff q 2).mpr ⟨!![0, 0; 1, 0], by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [kF, vElt, pow_one, Matrix.one_fin_two]⟩

omit [NeZero q] in
theorem kH_mem : kH q ∈ congFilt q 2 1 :=
  (mem_congFilt_iff q 2).mpr ⟨!![1, 0; 0, -1], by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [kH_coe, pow_one, Matrix.one_fin_two, sub_eq_add_neg]⟩

omit [NeZero q] in

theorem kE_pow_q : (kE q) ^ q = 1 :=
  congFilt_pow_q_eq_one q 2 (by omega) (kE_mem q)

omit [NeZero q] in

theorem one_add_q_smul_pow {g : SL(2, ZMod (q ^ 2))}
    {X : Matrix (Fin 2) (Fin 2) (ZMod (q ^ 2))}
    (hg : (g : Matrix (Fin 2) (Fin 2) (ZMod (q ^ 2))) = 1 + (q : ZMod (q ^ 2)) • X)
    (n : ℕ) :
    ((g ^ n : SL(2, ZMod (q ^ 2))) : Matrix (Fin 2) (Fin 2) (ZMod (q ^ 2)))
      = 1 + ((n * q : ℕ) : ZMod (q ^ 2)) • X := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [_root_.pow_succ g k, sl2coe_mul', ih, hg]
    have hkq : ((k * q : ℕ) : ZMod (q^2)) • X * ((q : ZMod (q^2)) • X) = 0 := by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Nat.cast_mul, mul_assoc,
        ← sq, q_sq_eq_zero q, mul_zero, zero_smul]
    rw [add_mul, one_mul, mul_add, mul_one, hkq, add_zero, add_assoc, ← add_smul]
    congr 2
    push_cast; ring

variable {q}

omit [NeZero q] in

theorem uElt_pow {R : Type*} [CommRing R] (b : R) (n : ℕ) :
    (uElt b) ^ n = uElt ((n : R) * b) := by
  induction n with
  | zero =>
    apply Matrix.SpecialLinearGroup.ext; intro i j
    simp [uElt, Matrix.one_fin_two]
  | succ k ih =>
    rw [_root_.pow_succ, ih, ← uElt_add, Nat.cast_succ, add_mul, one_mul]

omit [NeZero q] in

theorem vElt_pow {R : Type*} [CommRing R] (c : R) (n : ℕ) :
    (vElt c) ^ n = vElt ((n : R) * c) := by
  induction n with
  | zero =>
    apply Matrix.SpecialLinearGroup.ext; intro i j
    simp [vElt, Matrix.one_fin_two]
  | succ k ih =>
    rw [_root_.pow_succ, ih]
    apply Matrix.SpecialLinearGroup.ext; intro i j
    simp only [vElt, sl2coe_mul', sl2coe_mk',
      Nat.cast_succ]
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]
    all_goals ring

omit [NeZero q] in

theorem hElt_inv_mul_kH_mul_hElt (t : (ZMod (q^2))ˣ) :
    (hElt t)⁻¹ * kH q * hElt t = kH q := by
  have hinv : (hElt t)⁻¹ = hElt t⁻¹ := by
    apply Matrix.SpecialLinearGroup.ext; intro i j
    rw [SL2_inv_expl]; fin_cases i <;> (fin_cases j <;> simp [hElt])
  have htt : (t : ZMod (q^2)) * ↑t⁻¹ = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have htt' : (↑t⁻¹ : ZMod (q^2)) * ↑t = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  apply Matrix.SpecialLinearGroup.ext; intro i j
  rw [hinv]
  simp only [sl2coe_mul', hElt_coe, kH_coe, inv_inv]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  all_goals
    first
    | linear_combination (q : ZMod (q^2)) * htt + htt
    | linear_combination - (q : ZMod (q^2)) * htt' + htt'

omit [NeZero q] in
theorem weyl2_inv :
    (weyl2 q)⁻¹ = ⟨!![(0 : ZMod (q^2)), 1; -1, 0], by rw [Matrix.det_fin_two_of]; ring⟩ := by
  apply Matrix.SpecialLinearGroup.ext; intro i j
  rw [SL2_inv_expl]
  fin_cases i <;> fin_cases j <;> simp [weyl2]

omit [NeZero q] in
theorem kH_inv_coe :
    (((kH q)⁻¹ : SL(2, ZMod (q^2))) : Matrix (Fin 2) (Fin 2) (ZMod (q^2)))
      = !![1 - (q : ZMod (q^2)), 0; 0, 1 + (q : ZMod (q^2))] := by
  rw [SL2_inv_expl]
  ext i j; fin_cases i <;> fin_cases j <;> simp [kH]

omit [NeZero q] in

theorem weyl2_conj_kE :
    weyl2 q * kE q * (weyl2 q)⁻¹ = (kF q)⁻¹ := by
  apply Matrix.SpecialLinearGroup.ext; intro i j
  rw [weyl2_inv, SL2_inv_expl]
  simp only [sl2coe_mul', kE_coe, kF_coe, weyl2]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

omit [NeZero q] in

theorem weyl2_conj_kF :
    weyl2 q * kF q * (weyl2 q)⁻¹ = (kE q)⁻¹ := by
  apply Matrix.SpecialLinearGroup.ext; intro i j
  rw [weyl2_inv, SL2_inv_expl]
  simp only [sl2coe_mul', kE_coe, kF_coe, weyl2]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

omit [NeZero q] in

theorem weyl2_conj_kH :
    weyl2 q * kH q * (weyl2 q)⁻¹ = (kH q)⁻¹ := by
  apply Matrix.SpecialLinearGroup.ext; intro i j
  rw [weyl2_inv, kH_inv_coe]
  simp only [sl2coe_mul', kH_coe, weyl2]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

variable (q)

omit [NeZero q] in

theorem one_add_q_smul_mul {A B : Matrix (Fin 2) (Fin 2) (ZMod (q^2))} :
    (1 + (q : ZMod (q^2)) • A) * (1 + (q : ZMod (q^2)) • B)
      = 1 + (q : ZMod (q^2)) • (A + B) := by
  rw [mul_add, mul_one, add_mul, one_mul, smul_add, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, ← sq, q_sq_eq_zero q, zero_smul, add_zero, add_assoc]

omit [NeZero q] in
private theorem kE_coe' : ((kE q : SL(2, ZMod (q^2))) : Matrix (Fin 2) (Fin 2) (ZMod (q^2)))
    = 1 + (q : ZMod (q^2)) • !![(0 : ZMod (q^2)), 1; 0, 0] := by
  rw [kE_coe, Matrix.one_fin_two]
  ext i j; fin_cases i <;> fin_cases j <;> simp

omit [NeZero q] in
private theorem kF_coe' : ((kF q : SL(2, ZMod (q^2))) : Matrix (Fin 2) (Fin 2) (ZMod (q^2)))
    = 1 + (q : ZMod (q^2)) • !![(0 : ZMod (q^2)), 0; 1, 0] := by
  rw [kF_coe, Matrix.one_fin_two]
  ext i j; fin_cases i <;> fin_cases j <;> simp

omit [NeZero q] in
private theorem kH_coe' : ((kH q : SL(2, ZMod (q^2))) : Matrix (Fin 2) (Fin 2) (ZMod (q^2)))
    = 1 + (q : ZMod (q^2)) • !![(1 : ZMod (q^2)), 0; 0, -1] := by
  rw [kH_coe, Matrix.one_fin_two]
  ext i j; fin_cases i <;> fin_cases j <;> simp [sub_eq_add_neg]

theorem congFilt_one_eq_closure_efh :
    congFilt q 2 1 = Subgroup.closure {kE q, kF q, kH q} := by
  haveI : NeZero (q ^ 2) := ⟨pow_ne_zero 2 (NeZero.ne q)⟩
  refine le_antisymm ?_ ?_
  · intro g hg
    rw [mem_congFilt_iff] at hg
    obtain ⟨X, hX⟩ := hg
    rw [pow_one] at hX

    have hdet := g.det_coe
    rw [hX, det_one_add_smul_fin_two, q_sq_eq_zero q, zero_mul, add_zero] at hdet
    have htr : (q : ZMod (q^2)) * (X 0 0 + X 1 1) = 0 := by
      rw [← Matrix.trace_fin_two]; linear_combination hdet

    have heq : g = (kH q) ^ (X 0 0).val * (kE q) ^ (X 0 1).val * (kF q) ^ (X 1 0).val := by
      apply Matrix.SpecialLinearGroup.ext; intro i j
      rw [sl2coe_mul', sl2coe_mul',
        one_add_q_smul_pow q (kH_coe' q) _, one_add_q_smul_pow q (kE_coe' q) _,
        one_add_q_smul_pow q (kF_coe' q) _, hX,
        show ((X 0 0).val * q : ℕ) = ((X 0 0).val : ℕ) * q from rfl,
        Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, mul_smul, mul_smul, mul_smul,
        smul_comm ((X 0 0).val : ZMod (q^2)) (q : ZMod (q^2)),
        smul_comm ((X 0 1).val : ZMod (q^2)) (q : ZMod (q^2)),
        smul_comm ((X 1 0).val : ZMod (q^2)) (q : ZMod (q^2)),
        one_add_q_smul_mul, one_add_q_smul_mul]
      have hval : ∀ z : ZMod (q^2), ((z.val : ℕ) : ZMod (q^2)) = z := fun z => by
        rw [ZMod.natCast_val, ZMod.cast_id]

      rw [Matrix.add_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply,
        smul_eq_mul, smul_eq_mul]
      congr 1
      fin_cases i <;> fin_cases j <;> simp [hval]

      linear_combination htr
    rw [heq]
    exact mul_mem (mul_mem
      (pow_mem (Subgroup.subset_closure (by simp)) _)
      (pow_mem (Subgroup.subset_closure (by simp)) _))
      (pow_mem (Subgroup.subset_closure (by simp)) _)
  · rw [Subgroup.closure_le]
    rintro x (rfl | rfl | rfl)
    · exact kE_mem q
    · exact kF_mem q
    · exact kH_mem q

end Elements
p2m_reactivate "P2MW.S_Ihara_sl2_zmod_sq_congruence_preimage_commute.Ihara"

section AbstractEngine

variable {E : Type*} [Group E]

theorem commutatorElement_mul_central_left {a b c : E} (hc : c ∈ Subgroup.center E) :
    ⁅a * c, b⁆ = ⁅a, b⁆ := by
  have h1 : b * c = c * b := Subgroup.mem_center_iff.mp hc b
  simp only [commutatorElement_def, _root_.mul_inv_rev]
  rw [show a * c * b * (c⁻¹ * a⁻¹) * b⁻¹ = a * (c * b * c⁻¹) * a⁻¹ * b⁻¹ from by group,
    ← h1, mul_assoc b, mul_inv_cancel, mul_one]

theorem commutatorElement_mul_left_of_central {a b c : E}
    (hbc : ⁅b, c⁆ ∈ Subgroup.center E) : ⁅a * b, c⁆ = ⁅a, c⁆ * ⁅b, c⁆ := by
  rw [commutatorElement_mul_left_eq_conj_mul]
  have h1 : a * ⁅b, c⁆ = ⁅b, c⁆ * a := Subgroup.mem_center_iff.mp hbc a
  have h2 : ⁅a, c⁆ * ⁅b, c⁆ = ⁅b, c⁆ * ⁅a, c⁆ := Subgroup.mem_center_iff.mp hbc ⁅a, c⁆
  rw [show a * ⁅b, c⁆ * a⁻¹ = ⁅b, c⁆ from by rw [h1, mul_assoc, mul_inv_cancel, mul_one], h2]

theorem commutatorElement_conj_of_central {a b g : E}
    (hab : ⁅a, b⁆ ∈ Subgroup.center E) : ⁅g * a * g⁻¹, g * b * g⁻¹⁆ = ⁅a, b⁆ := by
  rw [← conjugate_commutatorElement]
  have h1 : g * ⁅a, b⁆ = ⁅a, b⁆ * g := Subgroup.mem_center_iff.mp hab g
  rw [h1, mul_assoc, mul_inv_cancel, mul_one]

theorem commutatorElement_mul_central_right {a b c : E} (hc : c ∈ Subgroup.center E) :
    ⁅a, b * c⁆ = ⁅a, b⁆ := by
  rw [← commutatorElement_inv (g₁ := b * c), commutatorElement_mul_central_left hc,
    commutatorElement_inv]

theorem commutatorElement_mul_right_of_central {a b c : E}
    (hac : ⁅a, c⁆ ∈ Subgroup.center E) : ⁅a, b * c⁆ = ⁅a, b⁆ * ⁅a, c⁆ := by
  have hca : ⁅c, a⁆ ∈ Subgroup.center E := by rw [← commutatorElement_inv]; exact inv_mem hac
  rw [← commutatorElement_inv (g₁ := b * c), commutatorElement_mul_left_of_central hca,
    _root_.mul_inv_rev, commutatorElement_inv, commutatorElement_inv,
    (Subgroup.mem_center_iff.mp hac ⁅a, b⁆)]

theorem commutatorElement_inv_left_of_central {a b : E}
    (hab : ⁅a, b⁆ ∈ Subgroup.center E) : ⁅a⁻¹, b⁆ = ⁅a, b⁆⁻¹ := by
  have h : ⁅a⁻¹ * a, b⁆ = ⁅a⁻¹, b⁆ * ⁅a, b⁆ := commutatorElement_mul_left_of_central hab
  rw [inv_mul_cancel, commutatorElement_one_left] at h
  exact (eq_inv_of_mul_eq_one_left h.symm)

theorem commutatorElement_inv_right_of_central {a b : E}
    (hab : ⁅a, b⁆ ∈ Subgroup.center E) : ⁅a, b⁻¹⁆ = ⁅a, b⁆⁻¹ := by
  have hba : ⁅b, a⁆ ∈ Subgroup.center E := by rw [← commutatorElement_inv]; exact inv_mem hab
  rw [← commutatorElement_inv (g₁ := b⁻¹), commutatorElement_inv_left_of_central hba,
    commutatorElement_inv]

theorem commutatorElement_pow_left_of_central {a b : E} (n : ℕ)
    (hab : ⁅a, b⁆ ∈ Subgroup.center E) : ⁅a ^ n, b⁆ = ⁅a, b⁆ ^ n := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [_root_.pow_succ, commutatorElement_mul_left_of_central hab, ih, _root_.pow_succ]

end AbstractEngine
p2m_reactivate "P2MW.S_Ihara_sl2_zmod_sq_congruence_preimage_commute.Ihara"

variable {E : Type} [Group E]

theorem comap_congFilt_one_commute (π : E →* SL(2, ZMod (q ^ 2)))
    (hsurj : Function.Surjective π) (hcen : MonoidHom.ker π ≤ Subgroup.center E)
    (hq : q.Prime) (hq5 : 5 ≤ q) [NeZero q] :
    ∀ x ∈ (congFilt q 2 1).comap π, ∀ y ∈ (congFilt q 2 1).comap π, Commute x y := by

  set K := congFilt q 2 1 with hKdef
  set W := K.comap π with hW
  have hKW : ∀ a ∈ K, ∃ x ∈ W, π x = a := fun a ha => by
    obtain ⟨x, hx⟩ := hsurj a; exact ⟨x, by simp [hW, Subgroup.mem_comap, hx, ha], hx⟩
  have hβcen : ∀ x ∈ W, ∀ y ∈ W, ⁅x, y⁆ ∈ Subgroup.center E := fun x hx y hy => by
    apply hcen
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_commute]
    exact (congFilt_commutative q 2 (by omega) (π x) hx (π y) hy)
  have hliftL : ∀ x ∈ W, ∀ x' ∈ W, π x = π x' → ∀ y ∈ W, ⁅x, y⁆ = ⁅x', y⁆ := by
    intro x hx x' hx' hxx' y hy
    have hc : x'⁻¹ * x ∈ Subgroup.center E := hcen (by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hxx', inv_mul_cancel])
    rw [show x = x' * (x'⁻¹ * x) from by group, commutatorElement_mul_central_left hc]
  have hliftR : ∀ x ∈ W, ∀ y ∈ W, ∀ y' ∈ W, π y = π y' → ⁅x, y⁆ = ⁅x, y'⁆ := by
    intro x hx y hy y' hy' hyy'
    rw [← commutatorElement_inv (g₁ := y), hliftL y hy y' hy' hyy' x hx,
      commutatorElement_inv]

  obtain ⟨eE, heEW, heE⟩ := hKW (kE q) (hKdef ▸ kE_mem q)
  obtain ⟨fE, hfEW, hfE⟩ := hKW (kF q) (hKdef ▸ kF_mem q)
  obtain ⟨hE, hhEW, hhE⟩ := hKW (kH q) (hKdef ▸ kH_mem q)

  have hβq : ∀ x ∈ W, ∀ y ∈ W, ⁅x, y⁆ ^ q = 1 := by
    intro x hx y hy
    rw [← commutatorElement_pow_left_of_central q (hβcen x hx y hy)]
    have hxq : x ^ q ∈ Subgroup.center E := hcen (by
      rw [MonoidHom.mem_ker, map_pow]
      exact congFilt_pow_q_eq_one q 2 (by omega) (Subgroup.mem_comap.mp hx))
    exact commutatorElement_eq_one_iff_commute.mpr
      ((Subgroup.mem_center_iff.mp hxq y).symm)
  have heq1 : ∀ {x : E} {m : ℕ}, Nat.Coprime m q → x ^ m = 1 → x ^ q = 1 → x = 1 := by
    intro x m hco hm hn
    have hd := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hm) (orderOf_dvd_of_pow_eq_one hn)
    rw [hco] at hd
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hd)
  have hconj : ∀ (g : SL(2, ZMod (q^2))) {x y x' y' : E}, x ∈ W → y ∈ W →
      x' ∈ W → y' ∈ W → π x' = g * π x * g⁻¹ → π y' = g * π y * g⁻¹ →
      ⁅x', y'⁆ = ⁅x, y⁆ := by
    intro g x y x' y' hx hy hx' hy' hxx' hyy'
    obtain ⟨gE, hgE⟩ := hsurj g
    have hgxW : gE * x * gE⁻¹ ∈ W := Subgroup.mem_comap.mpr (by
      rw [map_mul, map_mul, map_inv, hgE, ← hxx']; exact Subgroup.mem_comap.mp hx')
    have hgyW : gE * y * gE⁻¹ ∈ W := Subgroup.mem_comap.mpr (by
      rw [map_mul, map_mul, map_inv, hgE, ← hyy']; exact Subgroup.mem_comap.mp hy')
    rw [hliftL x' hx' (gE * x * gE⁻¹) hgxW
        (by rw [map_mul, map_mul, map_inv, hgE, hxx']) y' hy',
      hliftR (gE * x * gE⁻¹) hgxW y' hy' (gE * y * gE⁻¹) hgyW
        (by rw [map_mul, map_mul, map_inv, hgE, hyy']),
      commutatorElement_conj_of_central (hβcen x hx y hy)]

  have h2co : Nat.Coprime 2 (q ^ 2) :=
    (Nat.coprime_primes Nat.prime_two hq).mpr (by omega) |>.pow_right 2
  set u2 : (ZMod (q ^ 2))ˣ := ZMod.unitOfCoprime 2 h2co with hu2
  have hu2c : ((u2 : ZMod (q ^ 2)) : ZMod (q ^ 2)) = 2 := ZMod.coe_unitOfCoprime 2 h2co
  have hEH : ⁅eE, hE⁆ = 1 := by
    refine heq1 (m := 3) ((Nat.coprime_primes Nat.prime_three hq).mpr (by omega))
      ?_ (hβq eE heEW hE hhEW)

    have h4 : ⁅eE, hE⁆ ^ 4 = ⁅eE, hE⁆ := by
      rw [← commutatorElement_pow_left_of_central 4 (hβcen eE heEW hE hhEW)]
      refine hconj (hElt u2)⁻¹ heEW hhEW (W.pow_mem heEW 4) hhEW ?_ ?_
      · rw [map_pow, heE, inv_inv,
          show kE q = uElt (R := ZMod (q^2)) q from rfl,
          hElt_inv_mul_uElt_mul_hElt u2 (q : ZMod (q^2)), uElt_pow, hu2c]
        norm_num
      · rw [hhE, inv_inv, hElt_inv_mul_kH_mul_hElt u2]
    have h3 : ⁅eE, hE⁆ ^ 3 * ⁅eE, hE⁆ = 1 * ⁅eE, hE⁆ := by
      rw [← _root_.pow_succ, h4, one_mul]
    exact mul_right_cancel h3

  have hFH : ⁅fE, hE⁆ = 1 := by
    have hwconj : ⁅fE⁻¹, hE⁻¹⁆ = ⁅eE, hE⁆ := by
      refine hconj (weyl2 q) heEW hhEW (W.inv_mem hfEW) (W.inv_mem hhEW) ?_ ?_
      · rw [map_inv, hfE, heE]; exact weyl2_conj_kE.symm
      · rw [map_inv, hhE]; exact weyl2_conj_kH.symm
    rw [commutatorElement_inv_left_of_central (hβcen fE hfEW _ (W.inv_mem hhEW)),
      commutatorElement_inv_right_of_central (hβcen fE hfEW hE hhEW)] at hwconj
    rw [inv_inv] at hwconj
    rw [hwconj, hEH]

  have hEF : ⁅eE, fE⁆ = 1 := by
    refine heq1 (m := 2) ((Nat.coprime_primes Nat.prime_two hq).mpr (by omega))
      ?_ (hβq eE heEW fE hfEW)
    have hwconj : ⁅fE⁻¹, eE⁻¹⁆ = ⁅eE, fE⁆ := by
      refine hconj (weyl2 q) heEW hfEW (W.inv_mem hfEW) (W.inv_mem heEW) ?_ ?_
      · rw [map_inv, hfE, heE]; exact weyl2_conj_kE.symm
      · rw [map_inv, heE, hfE]; exact weyl2_conj_kF.symm
    rw [commutatorElement_inv_left_of_central (hβcen fE hfEW _ (W.inv_mem heEW)),
      commutatorElement_inv_right_of_central (hβcen fE hfEW eE heEW),
      inv_inv, ← commutatorElement_inv] at hwconj
    rw [sq]; nth_rw 1 [← hwconj]; exact inv_mul_cancel _

  have hgen : ∀ a ∈ ({kE q, kF q, kH q} : Set _), ∀ b ∈ ({kE q, kF q, kH q} : Set _),
      ∀ x ∈ W, π x = a → ∀ y ∈ W, π y = b → ⁅x, y⁆ = 1 := by
    intro a ha b hb x hx hxa y hy hyb

    have hsw : ∀ {s : E} {g : SL(2, ZMod (q^2))}, s ∈ W → π s = g →
        ∀ {z : E}, z ∈ W → π z = g → ∀ {w : E}, w ∈ W → ⁅s, w⁆ = ⁅z, w⁆ := by
      intro s g hs hsg z hz hzg w hw
      exact hliftL s hs z hz (hsg.trans hzg.symm) w hw
    have hswR : ∀ {z : E}, z ∈ W → ∀ {s : E} {g : SL(2, ZMod (q^2))}, s ∈ W → π s = g →
        ∀ {w : E}, w ∈ W → π w = g → ⁅z, s⁆ = ⁅z, w⁆ := by
      intro z hz s g hs hsg w hw hwg
      exact hliftR z hz s hs w hw (hsg.trans hwg.symm)
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
      [(rw [hsw hx hxa heEW heE hy, hswR heEW hy hyb heEW heE]; simp);
       (rw [hsw hx hxa heEW heE hy, hswR heEW hy hyb hfEW hfE]; exact hEF);
       (rw [hsw hx hxa heEW heE hy, hswR heEW hy hyb hhEW hhE]; exact hEH);
       (rw [hsw hx hxa hfEW hfE hy, hswR hfEW hy hyb heEW heE];
         rw [← _root_.inv_inj, ← commutatorElement_inv] at hEF; simpa using hEF);
       (rw [hsw hx hxa hfEW hfE hy, hswR hfEW hy hyb hfEW hfE]; simp);
       (rw [hsw hx hxa hfEW hfE hy, hswR hfEW hy hyb hhEW hhE]; exact hFH);
       (rw [hsw hx hxa hhEW hhE hy, hswR hhEW hy hyb heEW heE];
         rw [← _root_.inv_inj, ← commutatorElement_inv] at hEH; simpa using hEH);
       (rw [hsw hx hxa hhEW hhE hy, hswR hhEW hy hyb hfEW hfE];
         rw [← _root_.inv_inj, ← commutatorElement_inv] at hFH; simpa using hFH);
       (rw [hsw hx hxa hhEW hhE hy, hswR hhEW hy hyb hhEW hhE]; simp)]

  have hK : K = Subgroup.closure {kE q, kF q, kH q} := hKdef ▸ congFilt_one_eq_closure_efh q
  intro x hx y hy
  rw [show (Commute x y ↔ ⁅x, y⁆ = 1) from commutatorElement_eq_one_iff_commute.symm]
  have hxK : π x ∈ Subgroup.closure {kE q, kF q, kH q} := hK ▸ hx
  have hyK : π y ∈ Subgroup.closure {kE q, kF q, kH q} := hK ▸ hy

  let P : (a b : SL(2, ZMod (q^2))) →
      a ∈ Subgroup.closure {kE q, kF q, kH q} →
      b ∈ Subgroup.closure {kE q, kF q, kH q} → Prop :=
    fun a b _ _ => ∀ x ∈ W, π x = a → ∀ y ∈ W, π y = b → ⁅x, y⁆ = 1
  suffices h : P (π x) (π y) hxK hyK from h x hx rfl y hy rfl
  refine Subgroup.closure_induction₂ (p := P) (fun a b ha hb => hgen a ha b hb)
    ?_ ?_ ?_ ?_ ?_ ?_ hxK hyK
  ·
    intro b _ x' hx' hx1 y' hy' _
    exact (commutatorElement_eq_one_iff_commute.mpr
      ((Subgroup.mem_center_iff.mp (hcen (π.mem_ker.mpr hx1)) y').symm))
  ·
    intro a _ x' _ _ y' _ hy1
    exact (commutatorElement_eq_one_iff_commute.mpr
      (Subgroup.mem_center_iff.mp (hcen (π.mem_ker.mpr hy1)) x'))
  ·
    intro a b c ha hb hc Pac Pbc x' hx' hxab y' hy' hyc
    obtain ⟨xa, hxaW, hxa⟩ := hKW a (hK ▸ ha)
    obtain ⟨xb, hxbW, hxb⟩ := hKW b (hK ▸ hb)
    rw [hliftL x' hx' (xa * xb) (W.mul_mem hxaW hxbW)
        (by rw [map_mul, hxa, hxb, hxab]) y' hy',
      commutatorElement_mul_left_of_central (hβcen xb hxbW y' hy'),
      Pac xa hxaW hxa y' hy' hyc, Pbc xb hxbW hxb y' hy' hyc, one_mul]
  ·
    intro b c a hb hc ha Pab Pac x' hx' hxa y' hy' hybc
    obtain ⟨yb, hybW, hyb⟩ := hKW b (hK ▸ hb)
    obtain ⟨yc, hycW, hyc⟩ := hKW c (hK ▸ hc)
    rw [hliftR x' hx' y' hy' (yb * yc) (W.mul_mem hybW hycW)
        (by rw [map_mul, hyb, hyc, hybc]),
      commutatorElement_mul_right_of_central (hβcen x' hx' yc hycW),
      Pab x' hx' hxa yb hybW hyb, Pac x' hx' hxa yc hycW hyc, one_mul]
  ·
    intro a b ha hb Pab x' hx' hxa y' hy' hyb
    obtain ⟨xa, hxaW, hxaE⟩ := hKW a (hK ▸ ha)
    rw [hliftL x' hx' xa⁻¹ (W.inv_mem hxaW)
        (by rw [map_inv, hxaE, hxa]) y' hy',
      commutatorElement_inv_left_of_central (hβcen xa hxaW y' hy'),
      Pab xa hxaW hxaE y' hy' hyb, inv_one]
  ·
    intro a b ha hb Pab x' hx' hxa y' hy' hyb
    obtain ⟨yb', hybW, hybE⟩ := hKW b (hK ▸ hb)
    rw [hliftR x' hx' y' hy' yb'⁻¹ (W.inv_mem hybW)
        (by rw [map_inv, hybE, hyb]),
      commutatorElement_inv_right_of_central (hβcen x' hx' yb' hybW),
      Pab x' hx' hxa yb' hybW hybE, inv_one]

end Ihara
p2m_reactivate "P2MW.S_Ihara_sl2_zmod_sq_congruence_preimage_commute.Ihara"

end Inl_P2B_M2WAbelian
p2m_reactivate "P2MW.S_Ihara_sl2_zmod_sq_congruence_preimage_commute.Ihara"

open scoped MatrixGroups

theorem solution (q : ℕ)
    {E : Type} [Group E] (π : E →* SL(2, ZMod (q ^ 2)))
    (hsurj : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E)
    (hq : q.Prime) (hq5 : 5 ≤ q) :
    ∀ x, (∃ A : Matrix (Fin 2) (Fin 2) (ZMod (q ^ 2)),
        ((π x : SL(2, ZMod (q ^ 2))) : Matrix (Fin 2) (Fin 2) (ZMod (q ^ 2)))
          = 1 + (q : ZMod (q ^ 2)) • A) →
    ∀ y, (∃ B : Matrix (Fin 2) (Fin 2) (ZMod (q ^ 2)),
        ((π y : SL(2, ZMod (q ^ 2))) : Matrix (Fin 2) (Fin 2) (ZMod (q ^ 2)))
          = 1 + (q : ZMod (q ^ 2)) • B) →
    Commute x y := by
  haveI : NeZero q := ⟨by omega⟩
  intro x hx y hy
  have hxK : x ∈ (Ihara.congFilt q 2 1).comap π := by
    rw [Subgroup.mem_comap, Ihara.mem_congFilt_iff, pow_one]; exact hx
  have hyK : y ∈ (Ihara.congFilt q 2 1).comap π := by
    rw [Subgroup.mem_comap, Ihara.mem_congFilt_iff, pow_one]; exact hy
  exact Ihara.comap_congFilt_one_commute q π hsurj hcen hq hq5 x hxK y hyK

#print axioms solution

end S_Ihara_sl2_zmod_sq_congruence_preimage_commute
end P2MW
export P2MW.S_Ihara_sl2_zmod_sq_congruence_preimage_commute (solution)
