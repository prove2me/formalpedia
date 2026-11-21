-- Prove2me | solution 1 for GwExact.descCls_holds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T20:23:29.418173+00:00
-- url     : https://prove2.me/submissions/3ac171c5-739c-479f-b8dd-ba2582a8dfe3

module
public import Batteries.Tactic.Alias
public import Definitions.Def_GwExact_Check
public import Definitions.Def_GwExact_Clauses
public import Theorems.Thm_GwExact_testBit_bit
public import Theorems.Thm_P2M_GwExact_testBit_lor__e8313c48450e
public import Theorems.Thm_GwExact_monoMask_bit
public import Theorems.Thm_GwExact_rep_bit
public import Theorems.Thm_GwExact_holds_neg
public import Theorems.Thm_GwExact_holds_pos
public import Theorems.Thm_GwExact_not_beq_iff

set_option autoImplicit true
@[expose] public section
public section
open GwExact
namespace GwExact
theorem _root_.solution {n R l : Nat} {col : Nat → Nat} (hcol : GoodPos n R l col) (code : Nat)
    {cl : Cls} (h : descCls n R l code = some cl) : cl.Holds (asg R col) := by
  simp only [descCls, Bool.cond_eq_ite, Nat.beq_eq, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq,
    not_beq_iff, Nat.add_eq, Nat.mul_eq, Nat.sub_eq] at h
  generalize Nat.land code 7 = kind at h
  generalize Nat.land (Nat.shiftRight code 3) 255 = f1 at h
  generalize Nat.land (Nat.shiftRight code 11) 255 = f2 at h
  generalize Nat.land (Nat.shiftRight code 19) 255 = f3 at h
  generalize Nat.land (Nat.shiftRight code 27) 255 = f4 at h
  generalize Nat.land (Nat.shiftRight code 35) 255 = f5 at h
  have hR : ∀ i, col i < R := hcol.lt
  split at h
  · -- kind 0: some colour at position f1
    cases h
    have hc := hR f1
    refine holds_pos hc ?_ rfl
    show (Nat.shiftLeft (bit R - 1) (f1 * R)).testBit (f1 * R + col f1) = true
    have : bit R - 1 = 2 ^ R - 1 := by
      show (1 <<< R) - 1 = 2 ^ R - 1
      rw [Nat.one_shiftLeft]
    show ((bit R - 1) <<< (f1 * R)).testBit (f1 * R + col f1) = true
    rw [this, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
    simp [hc]
  split at h
  · -- kind 1: not two colours at position f1
    split at h
    · cases h
      rename_i hv
      obtain ⟨h23, h3R⟩ := hv
      by_cases ha : col f1 = f2
      · refine holds_neg (i := f1) (c := f3) h3R ?_ (by omega)
        show (Nat.lor (bit (f1 * R + f2)) (bit (f1 * R + f3))).testBit _ = true
        rw [testBit_lor', testBit_bit, testBit_bit]; simp
      · refine holds_neg (i := f1) (c := f2) (by omega) ?_ ha
        show (Nat.lor (bit (f1 * R + f2)) (bit (f1 * R + f3))).testBit _ = true
        rw [testBit_lor', testBit_bit, testBit_bit]; simp
    · cases h
  split at h
  · -- kind 2: no monochromatic l-term progression
    split at h
    · cases h
      rename_i hv
      obtain ⟨⟨hd, hn⟩, h3R⟩ := hv
      obtain ⟨j, hj, hne⟩ := hcol.mono f1 f2 hd hn
      by_cases ha : col f1 = f3
      · refine holds_neg (i := f1 + j * f2) (c := f3) h3R (monoMask_bit R f3 f1 f2 l j hj) ?_
        rw [← ha]; exact hne
      · refine holds_neg (i := f1 + 0 * f2) (c := f3) h3R (monoMask_bit R f3 f1 f2 l 0 (by omega)) ?_
        simpa using ha
    · cases h
  split at h
  · -- kind 3: no rainbow 3-term progression
    split at h
    · cases h
      rename_i hv
      obtain ⟨⟨⟨⟨⟨⟨⟨hd, hn⟩, h3⟩, h4⟩, h5⟩, h34⟩, h35⟩, h45⟩ := hv
      have bits : ∀ u, (Nat.lor (Nat.lor (bit (f1 * R + f3)) (bit ((f1 + f2) * R + f4)))
          (bit ((f1 + 2 * f2) * R + f5))).testBit u =
          (decide (f1 * R + f3 = u) || decide ((f1 + f2) * R + f4 = u) ||
            decide ((f1 + 2 * f2) * R + f5 = u)) := by
        intro u; rw [testBit_lor', testBit_lor', testBit_bit, testBit_bit, testBit_bit]
      by_cases e0 : col f1 = f3
      · by_cases e1 : col (f1 + f2) = f4
        · by_cases e2 : col (f1 + 2 * f2) = f5
          · exact absurd ⟨by omega, by omega, by omega⟩ (hcol.rb f1 f2 hd hn)
          · refine holds_neg (i := f1 + 2 * f2) (c := f5) h5 ?_ e2
            show (Nat.lor (Nat.lor _ _) _).testBit _ = true
            rw [bits]; simp
        · refine holds_neg (i := f1 + f2) (c := f4) h4 ?_ e1
          show (Nat.lor (Nat.lor _ _) _).testBit _ = true
          rw [bits]; simp
      · refine holds_neg (i := f1) (c := f3) h3 ?_ e0
        show (Nat.lor (Nat.lor _ _) _).testBit _ = true
        rw [bits]; simp
    · cases h
  split at h
  · -- kind 4: colour 0 at position 0
    split at h
    · cases h
      rename_i hR0
      refine holds_pos (i := 0) (c := 0) hR0 ?_ hcol.zero
      show (1 : Nat).testBit (0 * R + 0) = true
      simp
    · cases h
  split at h
  · -- kind 5: first-occurrence order
    split at h
    · cases h
      rename_i hv
      obtain ⟨h1c, hcR⟩ := hv
      by_cases hci : col f1 = f2
      · obtain ⟨j, hj, hj'⟩ := hcol.pred f1 (by omega)
        refine holds_pos (i := j) (c := f2 - 1) (by omega) ?_ (by omega)
        show (Nat.shiftLeft (rep R f1) (f2 - 1)).testBit (j * R + (f2 - 1)) = true
        show ((rep R f1) <<< (f2 - 1)).testBit (j * R + (f2 - 1)) = true
        rw [Nat.testBit_shiftLeft]
        simp only [Nat.le_add_left, decide_true, Bool.true_and, Nat.add_sub_cancel]
        exact rep_bit R f1 j hj
      · refine holds_neg (i := f1) (c := f2) hcR ?_ hci
        show (bit (f1 * R + f2)).testBit _ = true
        rw [testBit_bit]; simp
    · cases h
  · cases h
end GwExact
