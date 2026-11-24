-- Prove2me | solution 1 for GlobalTheory.UnipotentBorder.udl_exists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:01:44.499744+00:00
-- url     : https://prove2.me/submissions/11871014-ec8f-458a-9217-a6188b15a6bb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IwahoriFactorisation
import Theorems.Thm_GlobalTheory_UnipotentBorder_last_row
import Theorems.Thm_GlobalTheory_UnipotentBorder_last_col
import Theorems.Thm_GlobalTheory_UnipotentBorder_top_block
import Theorems.Thm_GlobalTheory_UnipotentBorder_border_ll
import Theorems.Thm_GlobalTheory_UnipotentBorder_border_lc
import Theorems.Thm_GlobalTheory_UnipotentBorder_border_cl
import Theorems.Thm_GlobalTheory_UnipotentBorder_border_cc
import Theorems.Thm_GlobalTheory_UnipotentBorder_border_top
import Theorems.Thm_GlobalTheory_UnipotentBorder_unit_sub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.UnipotentBorder
open Matrix
variable {O : Type} [CommRing O]
namespace GlobalTheory.UnipotentBorder
theorem _root_.solution [IsLocalRing O] {α β : O} (hβ : ¬IsUnit β) :
    ∀ (n : ℕ) (g : Matrix (Fin n) (Fin n) O),
    (∀ i j, (i < j → α ∣ g i j) ∧ (j < i → β ∣ g i j)) → (∀ i, IsUnit (g i i)) →
    ∃ (U : Matrix (Fin n) (Fin n) O) (D : Fin n → Oˣ) (L : Matrix (Fin n) (Fin n) O),
      (∀ i j, (j < i → U i j = 0) ∧ (i = j → U i j = 1) ∧ (i < j → α ∣ U i j)) ∧
      (∀ i j, (i < j → L i j = 0) ∧ (i = j → L i j = 1) ∧ (j < i → β ∣ L i j)) ∧
      g = U * diagonal (fun i => (D i : O)) * L := by
  intro n
  induction n with
  | zero =>
    intro g _ _
    exact ⟨0, fun i ↦ i.elim0, 0, fun i ↦ i.elim0, fun i ↦ i.elim0, Matrix.ext fun i _ ↦ i.elim0⟩
  | succ n ih =>
    intro g hg hd
    obtain ⟨u, hu⟩ := hd (Fin.last n)
    have hui : (↑u⁻¹ : O) * ↑u = 1 := Units.inv_mul u

    let g' : Matrix (Fin n) (Fin n) O := fun i j ↦
      g i.castSucc j.castSucc - (g i.castSucc (Fin.last n) * ↑u⁻¹) * g (Fin.last n) j.castSucc
    have hg' : ∀ i j, (i < j → α ∣ g' i j) ∧ (j < i → β ∣ g' i j) := by
      intro i j
      refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
      · exact dvd_sub ((hg _ _).1 (Fin.castSucc_lt_castSucc_iff.2 h))
          (Dvd.dvd.mul_right (Dvd.dvd.mul_right ((hg _ _).1 (Fin.castSucc_lt_last i)) _) _)
      · exact dvd_sub ((hg _ _).2 (Fin.castSucc_lt_castSucc_iff.2 h))
          (Dvd.dvd.mul_left ((hg _ _).2 (Fin.castSucc_lt_last j)) _)
    have hd' : ∀ i, IsUnit (g' i i) := fun i ↦
      unit_sub hβ (hd i.castSucc) ((hg _ _).2 (Fin.castSucc_lt_last i)) _
    obtain ⟨U0, D0, L0, hU0, hL0, hg0⟩ := ih g' hg' hd'
    let U := border U0 (fun i ↦ g i.castSucc (Fin.last n) * ↑u⁻¹) 0 1
    let L := border L0 0 (fun j ↦ ↑u⁻¹ * g (Fin.last n) j.castSucc) 1
    let D : Fin (n + 1) → Oˣ := Fin.lastCases u D0
    have hU : ∀ i j, (j < i → U i j = 0) ∧ (i = j → U i j = 1) ∧ (i < j → α ∣ U i j) := by
      intro i j
      rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl
      · rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
        · simp only [U, border_cc, Fin.castSucc_lt_castSucc_iff, Fin.castSucc_inj]
          exact hU0 i j
        · simp only [U, border_cl]
          exact ⟨fun h ↦ absurd h (not_lt.2 (Fin.castSucc_lt_last i).le),
            fun h ↦ absurd h (Fin.castSucc_lt_last i).ne,
            fun _ ↦ Dvd.dvd.mul_right ((hg _ _).1 (Fin.castSucc_lt_last i)) _⟩
      · rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
        · simp only [U, border_lc, Pi.zero_apply]
          exact ⟨fun _ ↦ trivial, fun h ↦ absurd h (Fin.castSucc_lt_last j).ne',
            fun h ↦ absurd h (not_lt.2 (Fin.castSucc_lt_last j).le)⟩
        · simp [U, border_ll]
    have hL : ∀ i j, (i < j → L i j = 0) ∧ (i = j → L i j = 1) ∧ (j < i → β ∣ L i j) := by
      intro i j
      rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl
      · rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
        · simp only [L, border_cc, Fin.castSucc_lt_castSucc_iff, Fin.castSucc_inj]
          exact hL0 i j
        · simp only [L, border_cl, Pi.zero_apply]
          exact ⟨fun _ ↦ trivial, fun h ↦ absurd h (Fin.castSucc_lt_last i).ne,
            fun h ↦ absurd h (not_lt.2 (Fin.castSucc_lt_last i).le)⟩
      · rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
        · simp only [L, border_lc]
          exact ⟨fun h ↦ absurd h (not_lt.2 (Fin.castSucc_lt_last j).le),
            fun h ↦ absurd h (Fin.castSucc_lt_last j).ne',
            fun _ ↦ Dvd.dvd.mul_left ((hg _ _).2 (Fin.castSucc_lt_last j)) _⟩
        · simp [L, border_ll]
    have hUU : IsUU U := fun i j ↦ ⟨(hU i j).1, (hU i j).2.1⟩
    have hLU : IsLU L := fun i j ↦ ⟨(hL i j).1, (hL i j).2.1⟩
    refine ⟨U, D, L, hU, hL, ?_⟩
    ext i j
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl
    · rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
      · rw [top_block]
        simp only [U, L, D, border_top, Fin.lastCases_castSucc, Fin.lastCases_last, border_cl, border_lc]
        rw [← hg0]
        simp only [g']
        linear_combination (-(g i.castSucc (Fin.last n) * ↑u⁻¹ * g (Fin.last n) j.castSucc)) * hui
      · rw [last_col hLU]
        simp only [U, D, border_cl, Fin.lastCases_last]
        linear_combination (-(g i.castSucc (Fin.last n))) * hui
    · rw [last_row hUU]
      rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
      · simp only [L, D, border_lc, Fin.lastCases_last]
        rw [← mul_assoc, Units.mul_inv, one_mul]
      · simp only [L, D, border_ll, Fin.lastCases_last, mul_one]
        exact hu.symm
end GlobalTheory.UnipotentBorder
