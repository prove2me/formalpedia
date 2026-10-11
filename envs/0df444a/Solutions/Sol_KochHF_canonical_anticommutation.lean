-- Prove2me | solution 1 for KochHF.canonical_anticommutation
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-10-10T16:34:38.726332+00:00
-- url     : https://prove2.me/submissions/b286242c-02fa-4081-a4af-291198a11ff1

import Mathlib
import Definitions.Def_KochHF_FockSpace


open Matrix KochHF

namespace KochHFAux

variable {K : ℕ}

lemma fermiSign_sq (i : Fin K) (S : Finset (Fin K)) : fermiSign i S * fermiSign i S = 1 := by
  unfold fermiSign; rw [← pow_add, ← two_mul, pow_mul]; simp

lemma star_fermiSign (i : Fin K) (S : Finset (Fin K)) : star (fermiSign i S) = fermiSign i S := by
  unfold fermiSign; simp

lemma fermiSign_insert (i j : Fin K) (S : Finset (Fin K)) (hj : j ∉ S) :
    fermiSign i (insert j S) = (if i < j then -1 else 1) * fermiSign i S := by
  unfold fermiSign
  rw [Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp [hj])]; ring
  · ring

lemma fermiSign_erase (i j : Fin K) (S : Finset (Fin K)) (hj : j ∈ S) :
    fermiSign i S = (if i < j then -1 else 1) * fermiSign i (S.erase j) := by
  conv_lhs => rw [← Finset.insert_erase hj]
  exact fermiSign_insert i j _ (by simp)

lemma mulVec_basisState (A : FockOp K) (S T : Finset (Fin K)) :
    (A *ᵥ basisState S) T = A T S := by
  simp [basisState, mulVec, dotProduct, Pi.single_apply]

lemma basisState_apply (S T : Finset (Fin K)) :
    basisState S T = if T = S then 1 else 0 := by
  simp [basisState, Pi.single_apply]

lemma op_ext {A B : FockOp K} (h : ∀ S, A *ᵥ basisState S = B *ᵥ basisState S) : A = B := by
  ext T S
  have := congrFun (h S) T
  rwa [mulVec_basisState, mulVec_basisState] at this

lemma cdag_basis (i : Fin K) (S : Finset (Fin K)) :
    cdag i *ᵥ basisState S = if i ∈ S then 0 else fermiSign i S • basisState (insert i S) := by
  funext T
  rw [mulVec_basisState]
  simp only [cdag, of_apply]
  split_ifs with h1 h2 h2 <;> simp_all [basisState_apply]

lemma cann_basis (i : Fin K) (S : Finset (Fin K)) :
    cann i *ᵥ basisState S =
      if i ∈ S then fermiSign i (S.erase i) • basisState (S.erase i) else 0 := by
  funext T
  rw [mulVec_basisState]
  simp only [cann, conjTranspose_apply, cdag, of_apply]
  split_ifs with h1 h2 h2
  · obtain ⟨h1, rfl⟩ := h1
    simp [basisState_apply, star_fermiSign, h1]
  · obtain ⟨h1, rfl⟩ := h1
    simp at h2
  · simp only [star_zero, Pi.smul_apply, basisState_apply, smul_eq_mul]
    split_ifs with h3
    · subst h3; exact absurd ⟨by simp, (Finset.insert_erase h2).symm⟩ h1
    · simp
  · simp

lemma cdag_cdag_basis (i j : Fin K) (S : Finset (Fin K)) :
    (cdag i * cdag j + cdag j * cdag i) *ᵥ basisState S = 0 := by
  rw [add_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, cdag_basis j, cdag_basis i]
  by_cases hij : i = j
  · subst hij
    split_ifs with h <;> simp_all [mulVec_smul, cdag_basis]
  by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;>
    simp [hi, hj, mulVec_smul, cdag_basis, hij, Ne.symm hij, smul_smul]
  rw [Finset.insert_comm, ← add_smul]
  rw [fermiSign_insert i j S hj, fermiSign_insert j i S hi]
  rcases lt_trichotomy i j with h | h | h
  · simp [h, h.not_gt]; left; ring
  · exact absurd h hij
  · simp [h, h.not_gt]; left; ring

lemma cdag_anticomm (i j : Fin K) : cdag i * cdag j + cdag j * cdag i = 0 :=
  op_ext fun S => by rw [cdag_cdag_basis, zero_mulVec]

lemma cann_anticomm (i j : Fin K) : cann i * cann j + cann j * cann i = 0 := by
  have := congrArg conjTranspose (cdag_anticomm i j)
  simpa [cann, conjTranspose_add, conjTranspose_mul, add_comm] using this

lemma cann_cdag_basis (i j : Fin K) (S : Finset (Fin K)) :
    (cann i * cdag j + cdag j * cann i) *ᵥ basisState S =
      (if i = j then 1 else 0) • basisState S := by
  rw [add_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, cdag_basis j, cann_basis i]
  by_cases hij : i = j
  · subst hij
    by_cases hi : i ∈ S
    · simp [hi, mulVec_smul, cdag_basis, smul_smul, fermiSign_sq, Finset.insert_erase hi]
    · simp [hi, mulVec_smul, cann_basis, smul_smul, fermiSign_sq]
  by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;>
    simp [hi, hj, mulVec_smul, cdag_basis, cann_basis, hij, Ne.symm hij, smul_smul]
  rw [Finset.erase_insert_of_ne (Ne.symm hij), ← add_smul]
  rw [fermiSign_insert i j _ (by simp [hj]), fermiSign_erase j i S hi]
  rcases lt_trichotomy i j with h | h | h
  · simp [h, h.not_gt]; left; ring
  · exact absurd h hij
  · simp [h, h.not_gt]; left; ring

lemma cann_cdag_anticomm (i j : Fin K) :
    cann i * cdag j + cdag j * cann i = if i = j then 1 else 0 :=
  op_ext fun S => by
    rw [cann_cdag_basis]; split_ifs <;> simp

lemma cann_vacuum (i : Fin K) : cann i *ᵥ vacuum K = 0 := by
  have : vacuum K = basisState ∅ := rfl
  rw [this, cann_basis]; simp

lemma cdagOrb_conjTranspose (φ : Fin K → ℂ) : (cdagOrb φ)ᴴ = cannOrb φ := by
  simp [cdagOrb, cannOrb, conjTranspose_sum, conjTranspose_smul, cann]

lemma cannOrb_conjTranspose (φ : Fin K → ℂ) : (cannOrb φ)ᴴ = cdagOrb φ := by
  rw [← cdagOrb_conjTranspose, conjTranspose_conjTranspose]

lemma bilin_anticomm (a b : Fin K → ℂ) (A B : Fin K → FockOp K) :
    (∑ μ, a μ • A μ) * (∑ ν, b ν • B ν) + (∑ ν, b ν • B ν) * (∑ μ, a μ • A μ) =
      ∑ μ, ∑ ν, (a μ * b ν) • (A μ * B ν + B ν * A μ) := by
  simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm, smul_add,
    Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_comm]
  simp [mul_comm]

lemma cannOrb_anticomm (φ χ : Fin K → ℂ) :
    cannOrb φ * cannOrb χ + cannOrb χ * cannOrb φ = 0 := by
  unfold cannOrb
  rw [bilin_anticomm]
  simp [cann_anticomm]

lemma cdagOrb_anticomm (φ χ : Fin K → ℂ) :
    cdagOrb φ * cdagOrb χ + cdagOrb χ * cdagOrb φ = 0 := by
  unfold cdagOrb
  rw [bilin_anticomm]
  simp [cdag_anticomm]

lemma cannOrb_cdagOrb_anticomm (φ χ : Fin K → ℂ) :
    cannOrb φ * cdagOrb χ + cdagOrb χ * cannOrb φ = orbInner φ χ • (1 : FockOp K) := by
  unfold cannOrb cdagOrb
  rw [bilin_anticomm]
  simp only [cann_cdag_anticomm, smul_ite, smul_zero]
  simp [orbInner, dotProduct, Finset.sum_smul]

lemma cannOrb_vacuum (φ : Fin K → ℂ) : cannOrb φ *ᵥ vacuum K = 0 := by
  simp [cannOrb, sum_mulVec, smul_mulVec, cann_vacuum]

lemma fockInner_vacuum : fockInner (vacuum K) (vacuum K) = 1 := by
  simp [fockInner, vacuum, dotProduct, Pi.single_apply]

end KochHFAux

namespace KochHFAux

theorem main_canonical_anticommutation {K : ℕ} (φ χ : Fin K → ℂ) :
    (cdagOrb φ)ᴴ = cannOrb φ ∧
    cannOrb φ * cannOrb χ + cannOrb χ * cannOrb φ = 0 ∧
    cdagOrb φ * cdagOrb χ + cdagOrb χ * cdagOrb φ = 0 ∧
    cannOrb φ * cdagOrb χ + cdagOrb χ * cannOrb φ = orbInner φ χ • (1 : FockOp K) ∧
    cannOrb φ *ᵥ vacuum K = 0 ∧
    fockInner (vacuum K) (vacuum K) = 1 :=
  ⟨cdagOrb_conjTranspose φ, cannOrb_anticomm φ χ, cdagOrb_anticomm φ χ,
    cannOrb_cdagOrb_anticomm φ χ, cannOrb_vacuum φ, fockInner_vacuum⟩

end KochHFAux

open Matrix KochHF

theorem solution {K : ℕ} (φ χ : Fin K → ℂ) :
    (cdagOrb φ)ᴴ = cannOrb φ ∧
    cannOrb φ * cannOrb χ + cannOrb χ * cannOrb φ = 0 ∧
    cdagOrb φ * cdagOrb χ + cdagOrb χ * cdagOrb φ = 0 ∧
    cannOrb φ * cdagOrb χ + cdagOrb χ * cannOrb φ = orbInner φ χ • (1 : FockOp K) ∧
    cannOrb φ *ᵥ vacuum K = 0 ∧
    fockInner (vacuum K) (vacuum K) = 1 := by
  exact KochHFAux.main_canonical_anticommutation φ χ
