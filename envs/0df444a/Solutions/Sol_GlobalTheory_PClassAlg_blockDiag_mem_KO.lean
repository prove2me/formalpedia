-- Prove2me | solution 1 for GlobalTheory.PClassAlg.blockDiag_mem_KO
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:41:52.100155+00:00
-- url     : https://prove2.me/submissions/494a3b11-596a-4350-a7ba-13b5fb968a49

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_DoubleBlockTriangularMemIntegralMulLevi
import Theorems.Thm_GlobalTheory_PClassAlg_shape_Xa
import Theorems.Thm_GlobalTheory_PClassAlg_eq_fromBlocks
import Theorems.Thm_GlobalTheory_PClassAlg_diag_block

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
noncomputable section
open GlobalTheory GlobalTheory.PClassAlg
namespace GlobalTheory.PClassAlg
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ϖ : kˣ) (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ), 1 ≤ p → p ≤ c → ∀ (A : GL (n ⊕ Fin c) k), A.val.BlockTriangular (Sum.elim (fun _ : n => 2 * p - 1) (fun i : Fin c => 2 * (i.val + 1))) → A.val.BlockTriangular (fun r => OrderDual.toDual (lev p r)) → (A⁻¹).val.BlockTriangular (Sum.elim (fun _ : n => 2 * p - 1) (fun i : Fin c => 2 * (i.val + 1))) → (A⁻¹).val.BlockTriangular (fun r => OrderDual.toDual (lev p r)) → (∀ i : Fin c, A.val (Sum.inr i) (Sum.inr i) * (ϖ : k) ^ (i.val + 1) ∈ 𝒪[k] ∧ (A⁻¹).val (Sum.inr i) (Sum.inr i) * ((ϖ : k) ^ (i.val + 1))⁻¹ ∈ 𝒪[k]) → (∀ i : Fin c, i.val + 1 = p → ∀ x : n, A.val (Sum.inl x) (Sum.inr i) * (ϖ : k) ^ (i.val + 1) ∈ 𝒪[k]) → ∃ γ : GL n k, A * embX c γ * embA n (GlobalTheory.SplitFlip.diagGL fun i : Fin c => ϖ ^ (i.val + 1)) ∈ KO k (n ⊕ Fin c) := by
  intro k _ _ _ _ ϖ n _ _ c p hp hpc A hA1 hA2 hB1 hB2 hD hE
  have eA := eq_fromBlocks hp _ hA1 hA2
  have eB := eq_fromBlocks hp _ hB1 hB2
  have dA := diag_block _ hA1 hA2
  have dB := diag_block _ hB1 hB2
  have sXa := shape_Xa _ hA1 hA2
  set P := toBlocks₁₁ A.val
  set Q := toBlocks₁₂ A.val
  set S := toBlocks₂₂ A.val
  set P' := toBlocks₁₁ (A⁻¹).val
  set Q' := toBlocks₁₂ (A⁻¹).val
  set S' := toBlocks₂₂ (A⁻¹).val
  have hAB : A.val * (A⁻¹).val = 1 := Units.mul_inv A
  have hBA : (A⁻¹).val * A.val = 1 := Units.inv_mul A
  rw [eA, eB, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_inj] at hAB hBA
  simp only [Matrix.mul_zero, add_zero, Matrix.zero_mul, zero_add] at hAB hBA
  obtain ⟨hPP', hPQ, -, -⟩ := hAB
  obtain ⟨hP'P, -, -, -⟩ := hBA
  let γ : GL n k := ⟨P', P, hP'P, hPP'⟩
  have hpow : ∀ i : Fin c, (((ϖ ^ (i.val + 1) : kˣ)) : k) = (ϖ : k) ^ (i.val + 1) := fun i => by simp
  have hne : ∀ i : Fin c, (ϖ : k) ^ (i.val + 1) ≠ 0 := fun i => pow_ne_zero _ ϖ.ne_zero
  refine ⟨γ, (GlobalTheory.SplitFlip.mem_KO_iff _).2 ⟨?_, ?_⟩⟩
  · have hM : (A * embX c γ * embA n (GlobalTheory.SplitFlip.diagGL fun i : Fin c => ϖ ^ (i.val + 1))).val =
        fromBlocks (P * P') (Q * diagonal fun i : Fin c => (ϖ : k) ^ (i.val + 1)) 0
          (S * diagonal fun i : Fin c => (ϖ : k) ^ (i.val + 1)) := by
      rw [Units.val_mul, Units.val_mul, eA]
      show fromBlocks P Q 0 S * fromBlocks P' 0 0 1 * fromBlocks 1 0 0 (GlobalTheory.SplitFlip.diagGL fun i : Fin c => ϖ ^ (i.val + 1)).val = _
      simp [fromBlocks_multiply, hpow]
    rw [hM, hPP']
    rintro (x | l) (y | i)
    · simp only [fromBlocks_apply₁₁, one_apply]; split_ifs <;> simp
    · simp only [fromBlocks_apply₁₂, mul_diagonal]
      by_cases h : i.val + 1 = p
      · exact hE i h x
      · simp [Q, toBlocks₁₂, sXa x i h]
    · simp
    · simp only [fromBlocks_apply₂₂, mul_diagonal, dA]
      by_cases h : l = i
      · subst h; simpa using (hD l).1
      · simp [diagonal_apply_ne _ h]

  · have hM : ((A * embX c γ * embA n (GlobalTheory.SplitFlip.diagGL fun i : Fin c => ϖ ^ (i.val + 1)))⁻¹).val =
        fromBlocks (P * P') (P * Q') 0
          ((diagonal fun i : Fin c => ((ϖ : k) ^ (i.val + 1))⁻¹) * S') := by
      rw [_root_.mul_inv_rev, _root_.mul_inv_rev, ← map_inv, ← map_inv, Units.val_mul, Units.val_mul, eB]
      show fromBlocks 1 0 0 ((GlobalTheory.SplitFlip.diagGL fun i : Fin c => ϖ ^ (i.val + 1))⁻¹).val *
        (fromBlocks P 0 0 1 * fromBlocks P' Q' 0 S') = _
      have : ((GlobalTheory.SplitFlip.diagGL fun i : Fin c => ϖ ^ (i.val + 1))⁻¹).val =
          diagonal fun i : Fin c => ((ϖ : k) ^ (i.val + 1))⁻¹ := by
        ext i j; simp [GlobalTheory.SplitFlip.diagGL, diagonal_apply]
      rw [this]
      simp [fromBlocks_multiply]
    have hPQ' : P * Q' = -(Q * S') := eq_neg_of_add_eq_zero_left hPQ
    rw [hM, hPP', hPQ', dB]
    rintro (x | l) (y | i)
    · simp only [fromBlocks_apply₁₁, one_apply]; split_ifs <;> simp
    · simp only [fromBlocks_apply₁₂, Matrix.neg_apply, mul_diagonal]
      by_cases h : i.val + 1 = p
      · have e : Q x i * (A⁻¹).val (Sum.inr i) (Sum.inr i) =
            (A.val (Sum.inl x) (Sum.inr i) * (ϖ : k) ^ (i.val + 1)) *
              ((A⁻¹).val (Sum.inr i) (Sum.inr i) * ((ϖ : k) ^ (i.val + 1))⁻¹) := by
          have := hne i
          simp only [Q, toBlocks₁₂, of_apply]
          field_simp
        rw [e]
        exact neg_mem (mul_mem (hE i h x) (hD i).2)
      · simp [Q, toBlocks₁₂, sXa x i h]
    · simp
    · simp only [fromBlocks_apply₂₂, diagonal_mul_diagonal, diagonal_apply]
      split_ifs with h
      · subst h; rw [mul_comm]; exact (hD l).2
      · exact zero_mem _
end GlobalTheory.PClassAlg
