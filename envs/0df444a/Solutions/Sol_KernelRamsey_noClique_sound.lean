-- Prove2me | solution 1 for KernelRamsey.noClique_sound
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-24T16:45:04.557437+00:00
-- url     : https://prove2.me/submissions/c86f931c-e2a8-4ae4-92ce-c1f8ee9efdce

import Mathlib
import Definitions.Def_KernelRamsey_Mask
open KernelRamsey

theorem solution {n : Nat} (rows : List Nat) :
    ∀ (f k cand : Nat), noClique rows f k cand = true →
      ∀ S : Finset (Fin n), S.card = k → (∀ v ∈ S, cand.testBit v.val = true) →
        ¬ IsMaskClique rows S := by
  intro f
  induction f with
  | zero =>
      intro k cand h S hS hsub hcl
      cases k with
      | zero => simp [noClique] at h
      | succ k =>
          simp only [noClique, beq_iff_eq] at h
          have hpos : 0 < S.card := by omega
          obtain ⟨v, hv⟩ := Finset.card_pos.mp hpos
          have := hsub v hv
          rw [h] at this
          simp at this
  | succ f ih =>
      intro k cand h S hS hsub hcl
      cases k with
      | zero => simp [noClique] at h
      | succ k =>
          by_cases hc : cand = 0
          · have hpos : 0 < S.card := by omega
            obtain ⟨v, hv⟩ := Finset.card_pos.mp hpos
            have := hsub v hv
            rw [hc] at this
            simp at this
          · have hne : (cand == 0) = false := by simpa using hc
            simp only [noClique, hne, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at h
            obtain ⟨h1, h2⟩ := h
            set p := Nat.log2 cand with hp
            by_cases hin : ∃ v ∈ S, v.val = p
            · obtain ⟨v, hvS, hvp⟩ := hin
              apply ih k _ h1 (S.erase v)
              · rw [Finset.card_erase_of_mem hvS]; omega
              · intro w hw
                have hwne : w ≠ v := Finset.ne_of_mem_erase hw
                have hwS : w ∈ S := Finset.mem_of_mem_erase hw
                have hwp : w.val ≠ p := by
                  intro heq; apply hwne; exact Fin.ext (by omega)
                rw [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_two_pow]
                have h3 := hsub w hwS
                have h4 : (row rows p).testBit w.val = true := by
                  have := hcl v hvS w hwS (Ne.symm hwne)
                  rwa [hvp] at this
                simp [h3, h4, Ne.symm hwp]
              · intro a ha b hb hab
                exact hcl a (Finset.mem_of_mem_erase ha) b (Finset.mem_of_mem_erase hb) hab
            · push Not at hin
              apply ih (k + 1) _ h2 S hS
              · intro w hw
                rw [Nat.testBit_xor, Nat.testBit_two_pow]
                have h3 := hsub w hw
                have hwp : p ≠ w.val := fun heq => hin w hw heq.symm
                simp [h3, hwp]
              · exact hcl
