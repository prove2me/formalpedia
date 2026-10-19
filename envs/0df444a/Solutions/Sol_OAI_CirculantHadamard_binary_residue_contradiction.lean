-- Prove2me | solution 1 for OAI.CirculantHadamard.binary_residue_contradiction
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T10:14:13.257995+00:00
-- url     : https://prove2.me/submissions/08ac50b2-b641-4d01-a7a1-6beb9e3e3ab2

import Mathlib
import Definitions.Def_CirculantHadamard
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Basic
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Witnesses
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_MatrixBridge
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicRing
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicNorm
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicProjection
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_LocalDVR
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_IntegerTwoLocal
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicEvaluation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicPolynomial
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_RamifiedConjugation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclotomicIntegerEvaluation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_DyadicRemainder
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_RamifiedEisenstein
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_RamifiedLocal
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_OrderHalving
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryBlocks
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryCoefficients
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclotomicRings
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_PrimeComponents
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_PrimeCharacterEvaluations
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryEvaluation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_LocalizationMaps
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryLocalization
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryLocalRing
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_AlternatingProducts
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryProductTransport
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_FirstOrderResidue
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryResidue

open OAI OAI.CirculantHadamard
universe uO uk uIota
open scoped BigOperators
variable {O : Type uO} [CommRing O]
variable {k : Type uk} [Field k] [charTwo : CharP k 2]
variable [IsDomain O]
theorem fo_mul {O K : Type*} [CommRing O] [Field K] (φ : O →+* K) (t : O) (hφt : φ t = 0) (a b : O) (A B : O) (ha : a = 1 + t * A)
    (hb : b = 1 + t * B) : a * b = 1 + t * (A + B + t * A * B) ∧
      φ (A + B + t * A * B) = φ A + φ B := by
  refine ⟨by rw [ha, hb]; ring, by simp [hφt]⟩

theorem fo_zpow {O K : Type*} [CommRing O] [Field K] (φ : O →+* K) (t : O) (hφt : φ t = 0) (u : Oˣ) (L : O)
    (hu : (u : O) = 1 + t * L) (n : ℤ) :
    ∃ M : O, ((u ^ n : Oˣ) : O) = 1 + t * M ∧ φ M = (n : K) * φ L := by
  have huinv : ((u⁻¹ : Oˣ) : O) = 1 + t * (-(L * ((u⁻¹ : Oˣ) : O))) := by
    have : ((u⁻¹ : Oˣ) : O) * (u : O) = 1 := Units.inv_mul u
    rw [hu] at this; linear_combination this
  have hφu : φ ((u⁻¹ : Oˣ) : O) = 1 := by
    have : φ ((u⁻¹ : Oˣ) : O) * φ (u : O) = 1 := by rw [← map_mul, Units.inv_mul, map_one]
    rw [hu, map_add, map_one, map_mul, hφt, zero_mul, add_zero, mul_one] at this; exact this
  induction n using Int.induction_on with
  | zero => exact ⟨0, by simp, by simp⟩
  | succ k ih =>
    obtain ⟨M, hM, hφM⟩ := ih
    obtain ⟨h1, h2⟩ := fo_mul φ t hφt _ _ M L hM hu
    refine ⟨_, ?_, h2.trans ?_⟩
    · rw [zpow_add_one, Units.val_mul, h1]
    · rw [hφM]; push_cast; ring
  | pred k ih =>
    obtain ⟨M, hM, hφM⟩ := ih
    obtain ⟨h1, h2⟩ := fo_mul φ t hφt _ _ M _ hM huinv
    refine ⟨_, ?_, h2.trans ?_⟩
    · rw [zpow_sub_one, Units.val_mul, h1]
    · rw [hφM, map_neg, map_mul, hφu]; push_cast; ring

theorem fo_main {O K : Type*} [CommRing O] [IsDomain O] [Field K] {ι : Type*}
    (φ : O →+* K) (t : O) (ht : t ≠ 0) (hφt : φ t = 0)
    (s : Finset ι) (u : ι → Oˣ) (L : ι → O) (ε : ι → ℤ)
    (hrep : ∀ i ∈ s, (u i : O) = 1 + t * L i)
    (hprod : (∏ i ∈ s, (u i) ^ (ε i)) = 1) :
    ∑ i ∈ s, (ε i : K) * φ (L i) = 0 := by
  classical
  have key : ∀ s' ⊆ s, ∃ M : O, ((∏ i ∈ s', (u i) ^ (ε i) : Oˣ) : O) = 1 + t * M ∧
      φ M = ∑ i ∈ s', (ε i : K) * φ (L i) := by
    intro s'
    induction s' using Finset.induction_on with
    | empty => intro _; exact ⟨0, by simp, by simp⟩
    | insert j s' hj ih =>
      intro hsub
      obtain ⟨M, hM, hφM⟩ := ih (fun x hx => hsub (Finset.mem_insert_of_mem hx))
      obtain ⟨N, hN, hφN⟩ := fo_zpow φ t hφt (u j) (L j) (hrep j (hsub (Finset.mem_insert_self _ _))) (ε j)
      obtain ⟨h1, h2⟩ := fo_mul φ t hφt _ _ N M hN hM
      refine ⟨_, ?_, h2.trans ?_⟩
      · rw [Finset.prod_insert hj, Units.val_mul, h1]
      · rw [hφN, hφM, Finset.sum_insert hj]
  obtain ⟨M, hM, hφM⟩ := key s le_rfl
  rw [hprod, Units.val_one] at hM
  have : t * M = 0 := by linear_combination -hM
  have hM0 : M = 0 := (mul_eq_zero.1 this).resolve_left ht
  rw [← hφM, hM0, map_zero]


theorem solution {ι : Type uIota}
    (φ : O →+* k) (i : O) (hi : i ^ 2 = -1) (hφi : φ i = 1)
    (h2 : (2 : O) ≠ 0) (s : Finset ι) (ε : ι → ℤ)
    (c d g : ι → Oˣ) (a b J U : ι → O)
    (hc : ∀ j ∈ s, (c j : O) = a j + b j)
    (hd : ∀ j ∈ s, (d j : O) = a j - b j)
    (hg : ∀ j ∈ s,
      (g j : O) = a j + i * b j - ((1 + i) * J j + 2 * U j))
    (hrOdd : ∃ m : ℕ, 0 < m ∧ Odd m ∧
      (∏ j ∈ s, (d j * (c j)⁻¹) ^ (ε j)) ^ m = 1)
    (hwOdd : ∃ m : ℕ, 0 < m ∧ Odd m ∧
      (∏ j ∈ s, (g j * (c j)⁻¹) ^ (ε j)) ^ m = 1)
    (hnonzero : (∑ j ∈ s, (ε j : k) * φ (J j * (↑((c j)⁻¹) : O))) ≠ 0) :
    False := by
  classical
  have h2t : (2 : O) = -i * (1 + i) ^ 2 := by linear_combination (i + 2) * hi
  have hφt : φ (1 + i) = 0 := by
    rw [map_add, map_one, hφi]; exact CharTwo.add_self_eq_zero 1
  have hφ2 : φ (2 : O) = 0 := by rw [map_ofNat]; exact CharTwo.two_eq_zero
  have ht0 : (1 + i) ≠ 0 := by
    intro h; apply h2; rw [h2t, h]; ring
  have hodd : ∀ m : ℕ, Odd m → (m : k) = 1 := by
    rintro m ⟨q, rfl⟩
    push_cast; rw [CharTwo.two_eq_zero]; ring
  have hcinv : ∀ j ∈ s, (c j : O) * ((c j)⁻¹ : Oˣ) = 1 := fun j _ => Units.mul_inv (c j)
  -- r: d/c = 1 + 2 * (-b c⁻¹)
  obtain ⟨m, hm0, hmodd, hm⟩ := hrOdd
  have hr := fo_main φ 2 h2 hφ2 s (fun j => d j * (c j)⁻¹) (fun j => -(b j * ((c j)⁻¹ : Oˣ)))
    (fun j => ε j * m)
    (by
      intro j hj
      simp only [Units.val_mul]
      rw [hd j hj]
      have := hcinv j hj
      rw [hc j hj] at this
      linear_combination this)
    (by
      rw [← hm, ← Finset.prod_pow]
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [zpow_mul, zpow_natCast])
  -- w: g/c = 1 + t * ((i b - J + i t U) c⁻¹)
  obtain ⟨m', hm0', hmodd', hm'⟩ := hwOdd
  have hw := fo_main φ (1 + i) ht0 hφt s (fun j => g j * (c j)⁻¹)
    (fun j => (i * b j - J j + i * (1 + i) * U j) * ((c j)⁻¹ : Oˣ))
    (fun j => ε j * m')
    (by
      intro j hj
      simp only [Units.val_mul]
      rw [hg j hj]
      have := hcinv j hj
      rw [hc j hj] at this
      linear_combination this + (-b j * ((c j)⁻¹ : Oˣ) - (i + 2) * U j * ((c j)⁻¹ : Oˣ)) * hi)
    (by
      rw [← hm', ← Finset.prod_pow]
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [zpow_mul, zpow_natCast])
  apply hnonzero
  simp only [Int.cast_mul, Int.cast_natCast, hodd m hmodd, hodd m' hmodd', mul_one] at hr hw
  simp only [map_neg, map_mul, map_add, map_sub, hφi, hφt, one_mul, mul_zero, zero_mul,
    add_zero] at hr hw
  have hr' : ∑ j ∈ s, (ε j : k) * φ (b j * ((c j)⁻¹ : Oˣ)) = 0 := by
    rw [← neg_eq_zero, ← Finset.sum_neg_distrib]
    simpa [map_mul] using hr
  have hfin : ∑ j ∈ s, (ε j : k) * φ (J j * ((c j)⁻¹ : Oˣ)) =
      ∑ j ∈ s, (ε j : k) * φ (b j * ((c j)⁻¹ : Oˣ)) -
        ∑ j ∈ s, (ε j : k) * ((φ (b j) - φ (J j)) * φ ((c j)⁻¹ : Oˣ)) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, map_mul]; ring
  rw [hfin, hr', hw, sub_zero]
