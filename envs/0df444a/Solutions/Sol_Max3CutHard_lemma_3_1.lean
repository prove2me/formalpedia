-- Prove2me | solution 1 for Max3CutHard.lemma_3_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T21:03:04.503078+00:00
-- url     : https://prove2.me/submissions/a0596980-3f66-4791-a041-c8f0622b6bdf

import Mathlib
import Definitions.Def_Max3CutHard_gadgetE
import Definitions.Def_Max3CutHard_gadgetN
import Definitions.Def_Max3CutHard_Gadget_gval
import Definitions.Def_Max3CutHard_sumX

namespace Aux_Max3Cut_l31
open Max3CutHard

def ne3 (u w : Fin 3) : ℕ := if u ≠ w then 1 else 0

def ne3' (u w : Fin 3) : ℕ := if u ≠ w then 3 else 0

def cE (x0 x1 x2 a0 a1 a2 a3 a4 a5 : Fin 3) : ℕ :=
  ne3 x0 a0 + (ne3 x0 a1 + (ne3 x0 a2 + (ne3 x0 a3 + (ne3 x1 a2 + (ne3 x1 a3 + (ne3 x1 a4 +
  (ne3 x1 a5 + (ne3 x2 a0 + (ne3 x2 a1 + (ne3 x2 a4 + (ne3 x2 a5 + (ne3 a0 a5 + (ne3 a0 a3 +
  (ne3 a1 a2 + (ne3 a1 a4 + (ne3 a2 a5 + (ne3 a3 a4 + 0)))))))))))))))))

def cN (x0 x1 x2 b : Fin 3) : ℕ :=
  ne3 x0 x1 + (ne3 x0 x2 + (ne3 x1 x2 + (ne3' b x0 + (ne3' b x1 + (ne3' b x2 + 0)))))

def ME (x0 x1 x2 : Fin 3) : ℕ := if x0 + x1 + x2 = 0 then 18 else 16
def MN (x0 x1 x2 : ZMod 3) : ℕ := if x0 + x1 + x2 ≠ 0 then 11 else 9

theorem ne3_le (u w : Fin 3) : ne3 u w ≤ 1 := by unfold ne3; split_ifs <;> omega

theorem cE_le18 (x0 x1 x2 a0 a1 a2 a3 a4 a5 : Fin 3) : cE x0 x1 x2 a0 a1 a2 a3 a4 a5 ≤ 18 := by
  calc cE x0 x1 x2 a0 a1 a2 a3 a4 a5 ≤ 1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 +
        (1 + (1 + (1 + (1 + (1 + (1 + 0))))))))))))))))) := by
        unfold cE
        gcongr <;> exact ne3_le _ _
    _ = 18 := by norm_num

theorem ne3_shift (u w c : Fin 3) : ne3 (u + c) (w + c) = ne3 u w := by
  unfold ne3; simp only [ne_eq, add_left_inj]

theorem cE_shift (c x0 x1 x2 a0 a1 a2 a3 a4 a5 : Fin 3) :
    cE (x0 + c) (x1 + c) (x2 + c) (a0 + c) (a1 + c) (a2 + c) (a3 + c) (a4 + c) (a5 + c) =
      cE x0 x1 x2 a0 a1 a2 a3 a4 a5 := by
  unfold cE; simp only [ne3_shift]

theorem three_c : ∀ c : Fin 3, c + c + c = 0 := by decide

theorem ME_shift (c x0 x1 x2 : Fin 3) : ME (x0 + c) (x1 + c) (x2 + c) = ME x0 x1 x2 := by
  unfold ME
  have : x0 + c + (x1 + c) + (x2 + c) = x0 + x1 + x2 + (c + c + c) := by abel
  rw [this, three_c, add_zero]

theorem factE0 : ∀ x1 x2 : Fin 3,
    (x1 + x2 ≠ 0 → ∀ a0 a1 a2 a3 a4 a5 : Fin 3, cE 0 x1 x2 a0 a1 a2 a3 a4 a5 ≤ 16) ∧
    ∃ a0 a1 a2 a3 a4 a5 : Fin 3, cE 0 x1 x2 a0 a1 a2 a3 a4 a5 = ME 0 x1 x2 := by
  decide +kernel

theorem factE : ∀ x0 x1 x2 : Fin 3,
    (∀ a0 a1 a2 a3 a4 a5 : Fin 3, cE x0 x1 x2 a0 a1 a2 a3 a4 a5 ≤ ME x0 x1 x2) ∧
    ∃ a0 a1 a2 a3 a4 a5 : Fin 3, cE x0 x1 x2 a0 a1 a2 a3 a4 a5 = ME x0 x1 x2 := by
  intro x0 x1 x2
  have key := factE0 (x1 + -x0) (x2 + -x0)
  have hx0 : x0 + -x0 = 0 := add_neg_cancel x0
  have hME : ME x0 x1 x2 = ME 0 (x1 + -x0) (x2 + -x0) := by
    rw [← hx0, ME_shift]
  refine ⟨fun a0 a1 a2 a3 a4 a5 => ?_, ?_⟩
  · rw [← cE_shift (-x0), hx0, hME]
    by_cases hs : (x1 + -x0) + (x2 + -x0) = 0
    · have : ME 0 (x1 + -x0) (x2 + -x0) = 18 := by unfold ME; rw [zero_add, if_pos hs]
      rw [this]; exact cE_le18 _ _ _ _ _ _ _ _ _
    · have : ME 0 (x1 + -x0) (x2 + -x0) = 16 := by unfold ME; rw [zero_add, if_neg hs]
      rw [this]; exact key.1 hs _ _ _ _ _ _
  · obtain ⟨a0, a1, a2, a3, a4, a5, h⟩ := key.2
    refine ⟨a0 - -x0, a1 - -x0, a2 - -x0, a3 - -x0, a4 - -x0, a5 - -x0, ?_⟩
    rw [← cE_shift (-x0), hx0, hME]
    simp only [sub_add_cancel]
    exact h

theorem factN : ∀ x0 x1 x2 : Fin 3,
    (∀ b : Fin 3, cN x0 x1 x2 b ≤ MN x0 x1 x2) ∧ ∃ b : Fin 3, cN x0 x1 x2 b = MN x0 x1 x2 := by
  decide +kernel

theorem ne3_cast (u w : Fin 3) : ((ne3 u w : ℕ) : ℝ) = if u ≠ w then 1 else 0 := by
  unfold ne3; split_ifs <;> simp

theorem ne3'_cast (u w : Fin 3) : ((ne3' u w : ℕ) : ℝ) = if u ≠ w then 3 else 0 := by
  unfold ne3'; split_ifs <;> simp

theorem gE (x : Fin 3 → Fin 3) (y : Fin 3 → Fin 3) :
    gadgetE.gval x y = (ME (x 0) (x 1) (x 2) : ℝ) := by
  have e : gadgetE.gval x y = Finset.univ.sup' Finset.univ_nonempty
      (fun z : Fin 6 → Fin 3 => cutR (Sum.elim x (Sum.elim y z))
        (let p : Fin 3 → Fin 3 ⊕ Fin 3 ⊕ Fin 6 := fun j => Sum.inl j
         let a : Fin 6 → Fin 3 ⊕ Fin 3 ⊕ Fin 6 := fun j => Sum.inr (Sum.inr j)
         [((p 0, a 0), 1), ((p 0, a 1), 1), ((p 0, a 2), 1), ((p 0, a 3), 1),
          ((p 1, a 2), 1), ((p 1, a 3), 1), ((p 1, a 4), 1), ((p 1, a 5), 1),
          ((p 2, a 0), 1), ((p 2, a 1), 1), ((p 2, a 4), 1), ((p 2, a 5), 1),
          ((a 0, a 5), 1), ((a 0, a 3), 1), ((a 1, a 2), 1), ((a 1, a 4), 1),
          ((a 2, a 5), 1), ((a 3, a 4), 1)] : RGraph (Fin 3 ⊕ Fin 3 ⊕ Fin 6))) := rfl
  have hcut : ∀ z : Fin 6 → Fin 3, cutR (Sum.elim x (Sum.elim y z))
        (let p : Fin 3 → Fin 3 ⊕ Fin 3 ⊕ Fin 6 := fun j => Sum.inl j
         let a : Fin 6 → Fin 3 ⊕ Fin 3 ⊕ Fin 6 := fun j => Sum.inr (Sum.inr j)
         [((p 0, a 0), 1), ((p 0, a 1), 1), ((p 0, a 2), 1), ((p 0, a 3), 1),
          ((p 1, a 2), 1), ((p 1, a 3), 1), ((p 1, a 4), 1), ((p 1, a 5), 1),
          ((p 2, a 0), 1), ((p 2, a 1), 1), ((p 2, a 4), 1), ((p 2, a 5), 1),
          ((a 0, a 5), 1), ((a 0, a 3), 1), ((a 1, a 2), 1), ((a 1, a 4), 1),
          ((a 2, a 5), 1), ((a 3, a 4), 1)] : RGraph (Fin 3 ⊕ Fin 3 ⊕ Fin 6)) =
      (cE (x 0) (x 1) (x 2) (z 0) (z 1) (z 2) (z 3) (z 4) (z 5) : ℝ) := by
    intro z
    simp only [cutR, cE, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Sum.elim_inl, Sum.elim_inr, Nat.cast_add, Nat.cast_zero, ne3_cast]
    rfl
  rw [e]
  obtain ⟨hle, a0, a1, a2, a3, a4, a5, heq⟩ := factE (x 0) (x 1) (x 2)
  apply le_antisymm
  · apply Finset.sup'_le
    intro z _
    rw [hcut z]
    exact_mod_cast hle (z 0) (z 1) (z 2) (z 3) (z 4) (z 5)
  · refine le_trans ?_ (Finset.le_sup' _ (Finset.mem_univ ![a0, a1, a2, a3, a4, a5]))
    rw [hcut]
    simp [heq]

theorem gN (x : Fin 3 → Fin 3) (y : Fin 3 → Fin 3) :
    gadgetN.gval x y = (MN (x 0) (x 1) (x 2) : ℝ) := by
  have e : gadgetN.gval x y = Finset.univ.sup' Finset.univ_nonempty
      (fun z : Fin 1 → Fin 3 => cutR (Sum.elim x (Sum.elim y z))
        (let p : Fin 3 → Fin 3 ⊕ Fin 3 ⊕ Fin 1 := fun j => Sum.inl j
         let q : Fin 3 ⊕ Fin 3 ⊕ Fin 1 := Sum.inr (Sum.inr 0)
         [((p 0, p 1), 1), ((p 0, p 2), 1), ((p 1, p 2), 1),
          ((q, p 0), 3), ((q, p 1), 3), ((q, p 2), 3)] : RGraph (Fin 3 ⊕ Fin 3 ⊕ Fin 1))) := rfl
  have hcut : ∀ z : Fin 1 → Fin 3, cutR (Sum.elim x (Sum.elim y z))
        (let p : Fin 3 → Fin 3 ⊕ Fin 3 ⊕ Fin 1 := fun j => Sum.inl j
         let q : Fin 3 ⊕ Fin 3 ⊕ Fin 1 := Sum.inr (Sum.inr 0)
         [((p 0, p 1), 1), ((p 0, p 2), 1), ((p 1, p 2), 1),
          ((q, p 0), 3), ((q, p 1), 3), ((q, p 2), 3)] : RGraph (Fin 3 ⊕ Fin 3 ⊕ Fin 1)) =
      (cN (x 0) (x 1) (x 2) (z 0) : ℝ) := by
    intro z
    simp only [cutR, cN, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Sum.elim_inl, Sum.elim_inr, Nat.cast_add, Nat.cast_zero, ne3_cast, ne3'_cast]
    rfl
  rw [e]
  obtain ⟨hle, b, heq⟩ := factN (x 0) (x 1) (x 2)
  apply le_antisymm
  · apply Finset.sup'_le
    intro z _
    rw [hcut z]
    exact_mod_cast hle (z 0)
  · refine le_trans ?_ (Finset.le_sup' _ (Finset.mem_univ ![b]))
    rw [hcut]
    simp [heq]

end Aux_Max3Cut_l31

open Max3CutHard Aux_Max3Cut_l31 in
theorem solution : ∀ (x : Fin 3 → ZMod 3) (y : Fin 3 → Fin 3),
    gadgetE.gval x y = (if sumX x = 0 then 18 else 16) ∧
    gadgetN.gval x y = (if sumX x ≠ 0 then 11 else 9) := by
  intro x y
  have h1 := gE x y
  have h2 := gN x y
  rw [h1, h2]
  constructor
  · by_cases hs : sumX x = 0
    · have e : ME (x 0) (x 1) (x 2) = 18 := by unfold ME; rw [if_pos (by exact hs)]
      rw [e, if_pos hs]; norm_num
    · have e : ME (x 0) (x 1) (x 2) = 16 := by unfold ME; rw [if_neg (by exact hs)]
      rw [e, if_neg hs]; norm_num
  · unfold MN sumX
    split_ifs <;> norm_num
