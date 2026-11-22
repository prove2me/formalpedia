-- Prove2me | solution 1 for MagicSquares.birkhoff_interior_count_eq_positive
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-22T02:00:01.13998+00:00
-- url     : https://prove2.me/submissions/29c27377-19f0-4071-9082-cd0d6c6394b2

import Mathlib
import Definitions.Def_MagicSquares
import Definitions.Def_MagicSquares_positiveInteriorCount
import Theorems.Thm_MagicSquares_positive_interior_small_zero

set_option autoImplicit false
set_option maxHeartbeats 0

open MagicSquares
open scoped BigOperators

/-- Standalone carrier mirroring `positiveInteriorCount`. -/
private noncomputable def car (n t : Nat) : Finset (Square n (Fin (t + 1))) :=
  by classical exact Finset.univ.filter fun M : Square n (Fin (t + 1)) =>
    IsSemiMagic (fun i j => (M i j : Nat)) t ∧ ∀ i j, 1 ≤ (M i j : Nat)

private lemma mem_car_iff {n t : Nat} {M : Square n (Fin (t + 1))} :
    M ∈ car n t ↔ M ∈ Finset.univ ∧
      (IsSemiMagic (fun i j => (M i j : Nat)) t ∧ ∀ i j, 1 ≤ (M i j : Nat)) := by
  unfold car
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- Coercion of a `Fin`-matrix to rationals. -/
private def fwd (n t : Nat) (M : Square n (Fin (t + 1))) : Matrix (Fin n) (Fin n) Rat :=
  fun i j => ((M i j : Nat) : Rat)

private lemma fwd_val (n t : Nat) (M : Square n (Fin (t + 1))) (i j : Fin n) :
    fwd n t M i j = ((M i j : Nat) : Rat) := rfl

private lemma fwd_inj (n t : Nat) : Function.Injective (fwd n t) := by
  intro A B h
  funext i j
  have h2 := congrFun (congrFun h i) j
  rw [fwd_val, fwd_val] at h2
  have h3 : (A i j : Nat) = (B i j : Nat) := Nat.cast_injective h2
  exact Fin.ext h3

theorem solution (n : Nat) (hn : 1 <= n) : forall t : Nat, Set.ncard {M : Matrix (Fin n) (Fin n) Rat | (exists D, D ∈ doublyStochastic Rat (Fin n) ∧ M = (t : Rat) • D) ∧ forall i j, 0 < M i j ∧ exists k : Nat, M i j = (k : Rat)} = positiveInteriorCount n t := by
  intro t
  show Set.ncard {M : Matrix (Fin n) (Fin n) Rat | (exists D, D ∈ doublyStochastic Rat (Fin n) ∧ M = (t : Rat) • D) ∧ forall i j, 0 < M i j ∧ exists k : Nat, M i j = (k : Rat)} = (car n t).card
  by_cases ht0 : t = 0
  · subst ht0
    have hL : {M : Matrix (Fin n) (Fin n) Rat | (exists D, D ∈ doublyStochastic Rat (Fin n) ∧ M = ((0 : Nat) : Rat) • D) ∧ forall i j, 0 < M i j ∧ exists k : Nat, M i j = (k : Rat)} = ∅ := by
      ext N
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨⟨D, hD, hND⟩, hpos⟩
      obtain ⟨i⟩ : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
      have hN0 : N = 0 := by
        have h0 : ((0 : Nat) : Rat) = 0 := Nat.cast_zero
        rw [h0, zero_smul] at hND
        exact hND
      have h2 := (hpos i i).1
      rw [hN0] at h2
      simp at h2
    have hR : (car n 0).card = 0 :=
      positive_interior_small_zero n 0 hn (by omega)
    rw [hL, Set.ncard_empty, hR]
  · have ht1 : 1 ≤ t := by omega
    have htQ : (t : Rat) ≠ 0 := by
      have hne : t ≠ 0 := by omega
      exact_mod_cast hne
    have hTS : {M : Matrix (Fin n) (Fin n) Rat | (exists D, D ∈ doublyStochastic Rat (Fin n) ∧ M = (t : Rat) • D) ∧ forall i j, 0 < M i j ∧ exists k : Nat, M i j = (k : Rat)} = ↑((car n t).image (fwd n t)) := by
      ext N
      simp only [Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_image]
      constructor
      · rintro ⟨⟨D, hD, hND⟩, hpos⟩
        have hbound : ∀ i j, ∃ k : Nat, N i j = (k : Rat) ∧ 1 ≤ k ∧ k ≤ t := by
          intro i j
          obtain ⟨k, hk⟩ := (hpos i j).2
          have hposij : (0 : Rat) < N i j := (hpos i j).1
          rw [hk] at hposij
          have hkpos : 1 ≤ k := by
            have hkp : 0 < k := by exact_mod_cast hposij
            omega
          have hkle : k ≤ t := by
            have hDle : D i j ≤ 1 := le_one_of_mem_doublyStochastic hD
            have hNij : N i j = (t : Rat) * D i j := by
              rw [hND, Matrix.smul_apply, smul_eq_mul]
            have hle : (k : Rat) ≤ (t : Rat) := by
              rw [← hk, hNij]
              calc (t : Rat) * D i j ≤ (t : Rat) * 1 :=
                    mul_le_mul_of_nonneg_left hDle (by positivity)
                _ = (t : Rat) := mul_one _
            exact_mod_cast hle
          exact ⟨k, hk, hkpos, hkle⟩
        choose k hk using hbound
        have hNrow : ∀ i, ∑ j, N i j = (t : Rat) := by
          intro i
          have e1 : ∑ j, N i j = ∑ j, (t : Rat) * D i j := by
            apply Finset.sum_congr rfl
            intro j _
            rw [hND, Matrix.smul_apply, smul_eq_mul]
          rw [e1, ← Finset.mul_sum, sum_row_of_mem_doublyStochastic hD i, mul_one]
        have hNcol : ∀ j, ∑ i, N i j = (t : Rat) := by
          intro j
          have e1 : ∑ i, N i j = ∑ i, (t : Rat) * D i j := by
            apply Finset.sum_congr rfl
            intro i _
            rw [hND, Matrix.smul_apply, smul_eq_mul]
          rw [e1, ← Finset.mul_sum, sum_col_of_mem_doublyStochastic hD j, mul_one]
        have hrowK : ∀ i, ∑ j, k i j = t := by
          intro i
          have e1 : (∑ j, ((k i j : Nat) : Rat)) = ∑ j, N i j :=
            Finset.sum_congr rfl (fun j _ => ((hk i j).1).symm)
          have e2 : (((∑ j, k i j : Nat)) : Rat) = ∑ j, (((k i j : Nat)) : Rat) := by simp
          have hcast : (((∑ j, k i j : Nat)) : Rat) = (((t : Nat)) : Rat) := by
            rw [e2, e1, hNrow i]
          exact Nat.cast_injective hcast
        have hcolK : ∀ j, ∑ i, k i j = t := by
          intro j
          have e1 : (∑ i, ((k i j : Nat) : Rat)) = ∑ i, N i j :=
            Finset.sum_congr rfl (fun i _ => ((hk i j).1).symm)
          have e2 : (((∑ i, k i j : Nat)) : Rat) = ∑ i, (((k i j : Nat)) : Rat) := by simp
          have hcast : (((∑ i, k i j : Nat)) : Rat) = (((t : Nat)) : Rat) := by
            rw [e2, e1, hNcol j]
          exact Nat.cast_injective hcast
        have hsemiK : IsSemiMagic (fun a b => k a b) t := by
          constructor
          · intro i
            simpa [rowSum] using hrowK i
          · intro j
            simpa [colSum] using hcolK j
        refine ⟨Matrix.of fun i j => (⟨k i j, by have h := (hk i j).2.2; omega⟩ : Fin (t + 1)), ?_, ?_⟩
        · rw [mem_car_iff]
          refine ⟨Finset.mem_univ _, ?_, ?_⟩
          · simp only [Matrix.of_apply]
            show IsSemiMagic (fun a b => k a b) t
            exact hsemiK
          · intro a b
            simp only [Matrix.of_apply]
            show 1 ≤ k a b
            exact (hk a b).2.1
        · funext i j
          show (((k i j : Nat)) : Rat) = N i j
          exact ((hk i j).1).symm
      · rintro ⟨M, hMC, rfl⟩
        obtain ⟨_, hsemi, hpos⟩ := mem_car_iff.mp hMC
        refine ⟨⟨(t : Rat)⁻¹ • fwd n t M, ?_, ?_⟩, fun i j => ⟨?_, ?_⟩⟩
        · refine mem_doublyStochastic_iff_sum.mpr ⟨?_, ?_, ?_⟩
          · intro i j
            have hnn : (0 : Rat) ≤ fwd n t M i j := by
              rw [fwd_val]
              positivity
            rw [Matrix.smul_apply, smul_eq_mul]
            exact mul_nonneg (inv_nonneg.mpr (by positivity)) hnn
          · intro i
            have h2 : ∑ j, (M i j : Nat) = t := by simpa [rowSum] using hsemi.1 i
            have hrow : ∑ j, (((M i j : Nat)) : Rat) = (t : Rat) := by exact_mod_cast h2
            have e1 : ∑ j, ((((t : Rat)⁻¹ • fwd n t M)) i j) = (t : Rat)⁻¹ * ∑ j, fwd n t M i j := by
              simp only [Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
            have e2 : ∑ j, fwd n t M i j = (t : Rat) := by
              calc ∑ j, fwd n t M i j = ∑ j, (((M i j : Nat)) : Rat) :=
                    Finset.sum_congr rfl (fun j _ => fwd_val n t M i j)
                _ = (t : Rat) := hrow
            rw [e1, e2, inv_mul_cancel₀ htQ]
          · intro j
            have h2 : ∑ i, (M i j : Nat) = t := by simpa [colSum] using hsemi.2 j
            have hcol : ∑ i, (((M i j : Nat)) : Rat) = (t : Rat) := by exact_mod_cast h2
            have e1 : ∑ i, ((((t : Rat)⁻¹ • fwd n t M)) i j) = (t : Rat)⁻¹ * ∑ i, fwd n t M i j := by
              simp only [Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
            have e2 : ∑ i, fwd n t M i j = (t : Rat) := by
              calc ∑ i, fwd n t M i j = ∑ i, (((M i j : Nat)) : Rat) :=
                    Finset.sum_congr rfl (fun i _ => fwd_val n t M i j)
                _ = (t : Rat) := hcol
            rw [e1, e2, inv_mul_cancel₀ htQ]
        · funext i j
          rw [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ htQ, one_mul]
        · have h1 : (1 : Rat) ≤ (((M i j : Nat)) : Rat) := by exact_mod_cast (hpos i j)
          rw [fwd_val]
          exact lt_of_lt_of_le zero_lt_one h1
        · exact ⟨(M i j : Nat), by rw [fwd_val]⟩
    have hcard : ((car n t).image (fwd n t)).card = (car n t).card :=
      Finset.card_image_of_injective _ (fwd_inj n t)
    rw [hTS, Set.ncard_coe_finset]
    exact hcard
