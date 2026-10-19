-- Prove2me | solution 1 for OAI.CirculantHadamard.first_order_sum_eq_zero_of_prod_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T10:05:38.32301+00:00
-- url     : https://prove2.me/submissions/d6c1c423-6728-45c3-89cd-3f7400ccd8a3

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

open OAI OAI.CirculantHadamard
universe uO uK uIota
open scoped BigOperators
variable {O : Type uO} [CommRing O]
variable [IsDomain O]
variable {K : Type uK} [Field K]
theorem fo_mul (φ : O →+* K) (t : O) (hφt : φ t = 0) (a b : O) (A B : O) (ha : a = 1 + t * A)
    (hb : b = 1 + t * B) : a * b = 1 + t * (A + B + t * A * B) ∧
      φ (A + B + t * A * B) = φ A + φ B := by
  refine ⟨by rw [ha, hb]; ring, by simp [hφt]⟩

theorem fo_zpow (φ : O →+* K) (t : O) (hφt : φ t = 0) (u : Oˣ) (L : O)
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


theorem solution {ι : Type uIota}
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
