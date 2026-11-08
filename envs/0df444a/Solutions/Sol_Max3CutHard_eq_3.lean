-- Prove2me | solution 1 for Max3CutHard.eq_3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T21:16:00.529553+00:00
-- url     : https://prove2.me/submissions/5488c9de-8c62-4896-8dd4-f87c9e6c5e06

import Mathlib
import Definitions.Def_Max3CutHard_family0
import Definitions.Def_Max3CutHard_Gadget_gval
import Definitions.Def_Max3CutHard_sumX
import Definitions.Def_Max3CutHard_betaT

namespace Aux_Max3Cut_eq3
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

theorem cut_scale {V : Type} {k : ℕ} (χ : V → Fin k) (G : RGraph V) (c : ℝ) :
    cutR χ (G.map fun e => (e.1, c * e.2)) = c * cutR χ G := by
  unfold cutR
  rw [List.map_map]
  induction G with
  | nil => simp
  | cons e G ih =>
    simp only [List.map_cons, List.sum_cons, Function.comp] at ih ⊢
    rw [ih]
    split_ifs <;> ring

theorem gval_scale {k : ℕ} [NeZero k] (I : Gadget k) (c : ℝ) (hc : 0 ≤ c)
    (x : Fin 3 → Fin k) (y : Fin k → Fin k) : (I.scale c).gval x y = c * I.gval x y := by
  unfold Gadget.gval Gadget.scale
  simp only [cut_scale]
  apply le_antisymm
  · apply Finset.sup'_le
    intro z _
    exact mul_le_mul_of_nonneg_left (Finset.le_sup' (fun z : Fin I.aux → Fin k =>
      cutR (Sum.elim x (Sum.elim y z)) I.edges) (Finset.mem_univ z)) hc
  · obtain ⟨z, _, hz⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := Fin I.aux → Fin k))
      (fun z : Fin I.aux → Fin k => cutR (Sum.elim x (Sum.elim y z)) I.edges)
    rw [hz]
    exact Finset.le_sup' (fun z : Fin I.aux → Fin k =>
      c * cutR (Sum.elim x (Sum.elim y z)) I.edges) (Finset.mem_univ z)

theorem gval_scale3 (I : Gadget 3) (c : ℝ) (hc : 0 ≤ c)
    (x : Fin 3 → ZMod 3) (y : Fin 3 → Fin 3) : (I.scale c).gval x y = c * I.gval x y :=
  gval_scale I c hc x y

theorem gE3 (x : Fin 3 → ZMod 3) (y : Fin 3 → Fin 3) :
    gadgetE.gval x y = (ME (x 0) (x 1) (x 2) : ℝ) := gE x y

theorem gN3 (x : Fin 3 → ZMod 3) (y : Fin 3 → Fin 3) :
    gadgetN.gval x y = (MN (x 0) (x 1) (x 2) : ℝ) := gN x y

end Aux_Max3Cut_eq3

open Max3CutHard Aux_Max3Cut_eq3 in
theorem solution : ∀ (t : ZMod 3) (x : Fin 3 → ZMod 3) (y : Fin 3 → Fin 3),
    (family0 t).gval x y =
      betaT t + 2 * ((if sumX x = t then 1 else 0) + (if sumX x = -t then 1 else 0)) := by
  intro t x y
  by_cases ht : t = 0
  · subst ht
    have e1 : family0 0 = gadgetE.scale 2 := by simp [family0]
    have e2 : betaT 0 = 32 := by simp [betaT]
    rw [e1, e2, gval_scale3 _ 2 (by norm_num), gE3]
    simp only [neg_zero]
    unfold ME
    by_cases hs : sumX x = 0
    · rw [if_pos (by exact hs), if_pos hs]; norm_num
    · rw [if_neg (by exact hs), if_neg hs]; norm_num
  · have e1 : family0 t = gadgetN := by simp [family0, ht]
    have e2 : betaT t = 9 := by simp [betaT, ht]
    rw [e1, e2, gN3]
    unfold MN
    have key : ∀ s t : ZMod 3, t ≠ 0 →
        ((s ≠ 0 → (s = t ∧ s ≠ -t) ∨ (s = -t ∧ s ≠ t)) ∧ (s = 0 → s ≠ t ∧ s ≠ -t)) := by
      decide
    obtain ⟨k1, k2⟩ := key (sumX x) t ht
    have hsx : sumX x = x 0 + x 1 + x 2 := rfl
    by_cases hs : sumX x = 0
    · have hs' : ¬ (x 0 + x 1 + x 2 ≠ 0) := by rw [← hsx]; exact not_not.mpr hs
      obtain ⟨h1, h2⟩ := k2 hs
      rw [if_neg hs', if_neg h1, if_neg h2]; norm_num
    · have hs' : x 0 + x 1 + x 2 ≠ 0 := by rw [← hsx]; exact hs
      rw [if_pos hs']
      rcases k1 hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [if_pos h1, if_neg h2]; norm_num
      · rw [if_neg h2, if_pos h1]; norm_num
