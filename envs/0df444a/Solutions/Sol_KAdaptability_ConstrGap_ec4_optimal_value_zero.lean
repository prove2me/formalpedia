-- Prove2me | solution 1 for KAdaptability.ConstrGap.ec4_optimal_value_zero
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:31:25.760129+00:00
-- url     : https://prove2.me/submissions/5d935877-abf5-486c-957c-5d0edc2ea4be

import Mathlib
import Definitions.Def_KAdaptability_ConstrGap_Problem
import Definitions.Def_KAdaptability_ConstrGap_Values
import Definitions.Def_KAdaptability_ConstrGap_Instance

set_option autoImplicit false
open Matrix KAdaptability.ConstrGap

theorem qqf_feasible (nQ : ℕ) (ξ : Fin (nQ + 1) → ℝ) (hξ : ec4A nQ *ᵥ ξ ≤ ec4b nQ) :
    ∃ y ∈ binaryCube nQ, ec4W nQ *ᵥ y ≤ ec4H nQ *ᵥ ξ := by
  obtain ⟨hb, hl⟩ := (ec4_Xi_iff nQ ξ).1 hξ
  refine ⟨boolVec (fun q => decide ((2:ℝ)⁻¹ ≤ ξ (Fin.castSucc q))), ?_, ?_⟩
  · simp [binaryCube]
  · intro l
    have hW : ∀ y : Fin nQ → ℝ, ∀ q : Fin nQ,
        (ec4W nQ *ᵥ y) (Fin.castAdd nQ q) = y q ∧ (ec4W nQ *ᵥ y) (Fin.natAdd nQ q) = - y q := by
      intro y q
      constructor
      · simp only [ec4W, mulVec, dotProduct, of_apply, Fin.addCases_left]
        simp
      · simp only [ec4W, mulVec, dotProduct, of_apply, Fin.addCases_right]
        simp
    have hH : ∀ q : Fin nQ,
        (ec4H nQ *ᵥ ξ) (Fin.castAdd nQ q) = ξ (Fin.castSucc q) + 1 / 2 ∧
        (ec4H nQ *ᵥ ξ) (Fin.natAdd nQ q) = - ξ (Fin.castSucc q) + 1 / 2 := by
      intro q
      constructor
      · simp only [ec4H, mulVec, dotProduct, of_apply, Fin.addCases_left]
        rw [Fin.sum_univ_castSucc]
        have hne : Fin.last nQ ≠ q.castSucc := (Fin.castSucc_lt_last q).ne'
        simp [Fin.castSucc_inj, hne, hl]
      · simp only [ec4H, mulVec, dotProduct, of_apply, Fin.addCases_right]
        rw [Fin.sum_univ_castSucc]
        have hne : Fin.last nQ ≠ q.castSucc := (Fin.castSucc_lt_last q).ne'
        simp [Fin.castSucc_inj, hne, hl]
    induction l using Fin.addCases with
    | left q =>
      rw [(hW _ q).1, (hH q).1]
      obtain ⟨hb1, hb2⟩ := hb q
      by_cases h : (2:ℝ)⁻¹ ≤ ξ (Fin.castSucc q) <;> simp [boolVec, h] <;> linarith
    | right q =>
      rw [(hW _ q).2, (hH q).2]
      obtain ⟨hb1, hb2⟩ := hb q
      by_cases h : (2:ℝ)⁻¹ ≤ ξ (Fin.castSucc q) <;> simp [boolVec, h] <;> linarith

theorem solution (nQ : ℕ) : (inst nQ).optP = 0 := by
  have hrec : ∀ (x : Fin 0 → ℝ) (ξ : Fin (nQ + 1) → ℝ), ξ ∈ (inst nQ).Xi →
      (inst nQ).recourse x ξ = 0 := by
    intro x ξ hξ
    obtain ⟨y, hy, hfe⟩ := qqf_feasible nQ ξ hξ
    apply le_antisymm
    · refine iInf_le_of_le y (iInf_le_of_le hy (iInf_le_of_le ?_ ?_))
      · have : (inst nQ).T *ᵥ x = 0 := by
          ext i; simp [inst, mulVec, dotProduct]
        rw [this, zero_add]; exact hfe
      · simp [inst]
    · refine le_iInf fun y => le_iInf fun _ => le_iInf fun _ => ?_
      simp [inst]
  have hobj : ∀ x : Fin 0 → ℝ, (inst nQ).objP x = 0 := by
    intro x
    apply le_antisymm
    · refine iSup_le fun ξ => iSup_le fun hξ => ?_
      rw [hrec x ξ hξ]; simp [inst]
    · obtain ⟨ξ0, h0⟩ := (inst nQ).Xi_nonempty
      refine le_iSup_of_le ξ0 (le_iSup_of_le h0 ?_)
      rw [hrec x ξ0 h0]; simp [inst]
  have hX : ∀ x : Fin 0 → ℝ, x ∈ (inst nQ).X := fun _ => Set.mem_univ _
  apply le_antisymm
  · exact iInf_le_of_le (fun i => i.elim0) (iInf_le_of_le (hX _) (hobj _).le)
  · exact le_iInf fun x => le_iInf fun _ => (hobj x).ge
