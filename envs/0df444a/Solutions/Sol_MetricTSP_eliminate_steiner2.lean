-- Prove2me | solution 1 for MetricTSP.eliminate_steiner2
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-25T04:53:52.829891+00:00
-- url     : https://prove2.me/submissions/f8785bfb-3ccd-40c7-bf59-0821caac0bbf

import Mathlib
import Definitions.Def_MetricTSP_model

set_option maxHeartbeats 1000000

namespace MetricTSP

open Finset

variable {n : ℕ}

/-! ### Cuts of integer multigraphs -/

/-- Directed mass between two vertex sets. -/
def mcross (H : Fin n → Fin n → ℕ) (A B : Finset (Fin n)) : ℕ :=
  ∑ u ∈ A, ∑ v ∈ B, H u v

/-- The cut of a vertex set. -/
def mcut (H : Fin n → Fin n → ℕ) (S : Finset (Fin n)) : ℕ := mcross H S Sᶜ

/-- Degree. -/
def mdeg (H : Fin n → Fin n → ℕ) (v : Fin n) : ℕ := ∑ u, H v u

/-- A set separating the terminal set `T`. -/
def TSep (T S : Finset (Fin n)) : Prop := (S ∩ T).Nonempty ∧ (Sᶜ ∩ T).Nonempty

lemma mcross_symm {H : Fin n → Fin n → ℕ} (hsym : ∀ u v, H u v = H v u)
    (A B : Finset (Fin n)) : mcross H A B = mcross H B A := by
  unfold mcross
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  exact hsym v u

lemma mcross_union_left {H : Fin n → Fin n → ℕ} {A B C : Finset (Fin n)}
    (hAB : Disjoint A B) : mcross H (A ∪ B) C = mcross H A C + mcross H B C := by
  unfold mcross
  rw [Finset.sum_union hAB]

lemma mcross_union_right {H : Fin n → Fin n → ℕ} {A B C : Finset (Fin n)}
    (hBC : Disjoint B C) : mcross H A (B ∪ C) = mcross H A B + mcross H A C := by
  unfold mcross
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u _
  rw [Finset.sum_union hBC]

lemma mcut_compl {H : Fin n → Fin n → ℕ} (hsym : ∀ u v, H u v = H v u)
    (S : Finset (Fin n)) : mcut H Sᶜ = mcut H S := by
  unfold mcut
  rw [compl_compl]
  exact mcross_symm hsym _ _

lemma TSep_compl {T S : Finset (Fin n)} (h : TSep T S) : TSep T Sᶜ := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨h2, ?_⟩
  rw [compl_compl]
  exact h1

/-- The two exact submodular cut identities. -/
lemma mcut_submod {H : Fin n → Fin n → ℕ} (hsym : ∀ u v, H u v = H v u)
    (S1 S2 : Finset (Fin n)) :
    mcut H S1 + mcut H S2
      = mcut H (S1 ∪ S2) + mcut H (S1 ∩ S2) + 2 * mcross H (S1 \ S2) (S2 \ S1)
    ∧ mcut H S1 + mcut H S2
      = mcut H (S1 \ S2) + mcut H (S2 \ S1)
        + 2 * mcross H (S1 ∩ S2) ((S1 ∪ S2)ᶜ) := by
  classical
  set A := S1 \ S2 with hA
  set B := S1 ∩ S2 with hB
  set C := S2 \ S1 with hC
  set D := (S1 ∪ S2)ᶜ with hD
  have memA : ∀ a, a ∈ A ↔ a ∈ S1 ∧ a ∉ S2 := fun a => by
    rw [hA, Finset.mem_sdiff]
  have memB : ∀ a, a ∈ B ↔ a ∈ S1 ∧ a ∈ S2 := fun a => by
    rw [hB, Finset.mem_inter]
  have memC : ∀ a, a ∈ C ↔ a ∈ S2 ∧ a ∉ S1 := fun a => by
    rw [hC, Finset.mem_sdiff]
  have memD : ∀ a, a ∈ D ↔ a ∉ S1 ∧ a ∉ S2 := fun a => by
    rw [hD, Finset.mem_compl, Finset.mem_union]
    tauto
  have dAB : Disjoint A B := Finset.disjoint_left.mpr (fun a ha hb =>
    ((memA a).mp ha).2 ((memB a).mp hb).2)
  have dAC : Disjoint A C := Finset.disjoint_left.mpr (fun a ha hb =>
    ((memC a).mp hb).2 ((memA a).mp ha).1)
  have dAD : Disjoint A D := Finset.disjoint_left.mpr (fun a ha hb =>
    ((memD a).mp hb).1 ((memA a).mp ha).1)
  have dBC : Disjoint B C := Finset.disjoint_left.mpr (fun a ha hb =>
    ((memC a).mp hb).2 ((memB a).mp ha).1)
  have dBD : Disjoint B D := Finset.disjoint_left.mpr (fun a ha hb =>
    ((memD a).mp hb).1 ((memB a).mp ha).1)
  have dCD : Disjoint C D := Finset.disjoint_left.mpr (fun a ha hb =>
    ((memD a).mp hb).2 ((memC a).mp ha).1)
  have hS1eq : S1 = A ∪ B := by
    ext a
    rw [Finset.mem_union, memA a, memB a]
    by_cases h2 : a ∈ S2 <;> tauto
  have hS1c : S1ᶜ = C ∪ D := by
    ext a
    rw [Finset.mem_compl, Finset.mem_union, memC a, memD a]
    by_cases h2 : a ∈ S2 <;> tauto
  have hS2eq : S2 = B ∪ C := by
    ext a
    rw [Finset.mem_union, memB a, memC a]
    by_cases h1 : a ∈ S1 <;> tauto
  have hS2c : S2ᶜ = A ∪ D := by
    ext a
    rw [Finset.mem_compl, Finset.mem_union, memA a, memD a]
    by_cases h1 : a ∈ S1 <;> tauto
  have hUeq : S1 ∪ S2 = (A ∪ B) ∪ C := by
    ext a
    rw [Finset.mem_union, Finset.mem_union, Finset.mem_union, memA a, memB a, memC a]
    by_cases h1 : a ∈ S1 <;> by_cases h2 : a ∈ S2 <;> tauto
  have hIc : Bᶜ = A ∪ (C ∪ D) := by
    ext a
    rw [Finset.mem_compl, Finset.mem_union, Finset.mem_union, memA a, memB a,
      memC a, memD a]
    by_cases h1 : a ∈ S1 <;> by_cases h2 : a ∈ S2 <;> tauto
  have hAc : Aᶜ = B ∪ (C ∪ D) := by
    ext a
    rw [Finset.mem_compl, Finset.mem_union, Finset.mem_union, memA a, memB a,
      memC a, memD a]
    by_cases h1 : a ∈ S1 <;> by_cases h2 : a ∈ S2 <;> tauto
  have hCc : Cᶜ = B ∪ (A ∪ D) := by
    ext a
    rw [Finset.mem_compl, Finset.mem_union, Finset.mem_union, memA a, memB a,
      memC a, memD a]
    by_cases h1 : a ∈ S1 <;> by_cases h2 : a ∈ S2 <;> tauto
  -- expansions
  have e1 : mcut H S1 = mcross H A C + mcross H A D
      + (mcross H B C + mcross H B D) := by
    unfold mcut
    rw [hS1c]
    conv_lhs => rw [hS1eq]
    rw [mcross_union_left dAB, mcross_union_right dCD, mcross_union_right dCD]
  have e2 : mcut H S2 = mcross H B A + mcross H B D
      + (mcross H C A + mcross H C D) := by
    unfold mcut
    rw [hS2c]
    conv_lhs => rw [hS2eq]
    rw [mcross_union_left dBC, mcross_union_right dAD, mcross_union_right dAD]
  have eU : mcut H (S1 ∪ S2) = mcross H A D + mcross H B D + mcross H C D := by
    unfold mcut
    rw [show (S1 ∪ S2)ᶜ = D from hD.symm ▸ rfl]
    conv_lhs => rw [hUeq]
    rw [mcross_union_left (Finset.disjoint_union_left.mpr ⟨dAC, dBC⟩),
      mcross_union_left dAB]
  have eI : mcut H (S1 ∩ S2) = mcross H B A + (mcross H B C + mcross H B D) := by
    unfold mcut
    show mcross H B Bᶜ = _
    rw [hIc, mcross_union_right (Finset.disjoint_union_right.mpr ⟨dAC, dAD⟩),
      mcross_union_right dCD]
  have eA : mcut H A = mcross H A B + (mcross H A C + mcross H A D) := by
    unfold mcut
    rw [hAc, mcross_union_right (Finset.disjoint_union_right.mpr ⟨dBC, dBD⟩),
      mcross_union_right dCD]
  have eC : mcut H C = mcross H C B + (mcross H C A + mcross H C D) := by
    unfold mcut
    rw [hCc, mcross_union_right (Finset.disjoint_union_right.mpr ⟨dAB.symm, dBD⟩),
      mcross_union_right dAD]
  have sAC : mcross H C A = mcross H A C := mcross_symm hsym C A
  have sAB : mcross H B A = mcross H A B := mcross_symm hsym B A
  have sBC : mcross H C B = mcross H B C := mcross_symm hsym C B
  have hcrossD : mcross H (S1 ∩ S2) ((S1 ∪ S2)ᶜ) = mcross H B D := by
    show mcross H B D = _
    rfl
  constructor
  · rw [e1, e2, eU, eI, sAC, sAB]
    ring
  · rw [e1, e2, eA, eC, hcrossD, sAC, sAB, sBC]
    ring

/-! ### The splitting operation -/

/-- Mass added by splitting `(v,u),(v,w) → (u,w)` (nothing when `u = w`). -/
def addM (u w : Fin n) : Fin n → Fin n → ℕ :=
  fun a b => if u ≠ w ∧ ((a = u ∧ b = w) ∨ (a = w ∧ b = u)) then 1 else 0

/-- Mass removed by splitting at `v` the pair `(u, w)`. -/
def subM (v u w : Fin n) : Fin n → Fin n → ℕ :=
  fun a b => (if a = v then (if b = u then 1 else 0) + (if b = w then 1 else 0) else 0)
    + (if b = v then (if a = u then 1 else 0) + (if a = w then 1 else 0) else 0)

/-- The split multigraph. -/
def splitH (H : Fin n → Fin n → ℕ) (v u w : Fin n) : Fin n → Fin n → ℕ :=
  fun a b => H a b + addM u w a b - subM v u w a b

section SplitFacts

variable {H : Fin n → Fin n → ℕ} {v u w : Fin n}

/-- The removed mass is dominated pointwise. -/
lemma subM_le (hsym : ∀ a b, H a b = H b a)
    (hvu : u ≠ v) (hvw : w ≠ v)
    (hau : 1 ≤ H v u) (haw : 1 ≤ H v w) (hauw : u = w → 2 ≤ H v u) :
    ∀ a b, subM v u w a b ≤ H a b + addM u w a b := by
  intro a b
  unfold subM addM
  by_cases hav : a = v <;> by_cases hbv : b = v
  · -- a = b = v : both inner sums vanish since u, w ≠ v
    rw [if_pos hav, if_pos hbv]
    rw [if_neg (show ¬ b = u by rw [hbv]; exact fun h => hvu h.symm),
      if_neg (show ¬ b = w by rw [hbv]; exact fun h => hvw h.symm),
      if_neg (show ¬ a = u by rw [hav]; exact fun h => hvu h.symm),
      if_neg (show ¬ a = w by rw [hav]; exact fun h => hvw h.symm)]
    omega
  · rw [if_pos hav, if_neg hbv]
    by_cases hbu : b = u
    · rw [if_pos hbu]
      by_cases hbw : b = w
      · -- b = u = w : need 2 ≤ H v u
        have huw : u = w := hbu.symm.trans hbw
        have h2 := hauw huw
        rw [if_pos hbw, hav, hbu]
        omega
      · have huw : u ≠ w := fun h => hbw (hbu.trans h)
        rw [if_neg hbw, hav, hbu]
        omega
    · rw [if_neg hbu]
      by_cases hbw : b = w
      · rw [if_pos hbw, hav, hbw]
        have h1 : H v w ≥ 1 := haw
        omega
      · rw [if_neg hbw]
        omega
  · rw [if_neg hav, if_pos hbv]
    by_cases hau' : a = u
    · rw [if_pos hau']
      by_cases haw' : a = w
      · have huw : u = w := hau'.symm.trans haw'
        have h2 := hauw huw
        rw [if_pos haw', hbv, hau']
        have := hsym u v
        omega
      · rw [if_neg haw', hbv, hau']
        have := hsym u v
        omega
    · rw [if_neg hau']
      by_cases haw' : a = w
      · rw [if_pos haw', hbv, haw']
        have := hsym w v
        omega
      · rw [if_neg haw']
        omega
  · rw [if_neg hav, if_neg hbv]
    omega

/-- Pointwise accounting identity for the split. -/
lemma splitH_add (hsym : ∀ a b, H a b = H b a)
    (hvu : u ≠ v) (hvw : w ≠ v)
    (hau : 1 ≤ H v u) (haw : 1 ≤ H v w) (hauw : u = w → 2 ≤ H v u)
    (a b : Fin n) :
    splitH H v u w a b + subM v u w a b = H a b + addM u w a b := by
  have h := subM_le (H := H) (v := v) (u := u) (w := w) hsym hvu hvw hau haw hauw a b
  unfold splitH
  omega

lemma addM_symm (a b : Fin n) : addM u w a b = addM u w b a := by
  unfold addM
  by_cases h : u ≠ w ∧ ((a = u ∧ b = w) ∨ (a = w ∧ b = u))
  · rw [if_pos h, if_pos ⟨h.1, h.2.symm.imp (fun hh => ⟨hh.2, hh.1⟩)
      (fun hh => ⟨hh.2, hh.1⟩)⟩]
  · rw [if_neg h, if_neg (fun hh : u ≠ w ∧ ((b = u ∧ a = w) ∨ (b = w ∧ a = u)) =>
      h ⟨hh.1, hh.2.symm.imp (fun h2 => ⟨h2.2, h2.1⟩) (fun h2 => ⟨h2.2, h2.1⟩)⟩)]

lemma subM_symm (a b : Fin n) : subM v u w a b = subM v u w b a := by
  unfold subM
  ring

lemma splitH_symm (hsym : ∀ a b, H a b = H b a) (a b : Fin n) :
    splitH H v u w a b = splitH H v u w b a := by
  unfold splitH
  rw [hsym a b, addM_symm, subM_symm]

lemma addM_diag (a : Fin n) : addM u w a a = 0 := by
  unfold addM
  rw [if_neg]
  rintro ⟨hne, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
  · exact hne (h1.symm.trans h2)
  · exact hne (h2.symm.trans h1)

lemma splitH_diag (hdiag : ∀ a, H a a = 0) (a : Fin n) :
    splitH H v u w a a = 0 := by
  unfold splitH
  rw [hdiag a, addM_diag]
  omega

/-- Row sums of the added mass. -/
lemma addM_row (x : Fin n) : ∑ b, addM u w x b
    = if u ≠ w then (if x = u then 1 else 0) + (if x = w then 1 else 0) else 0 := by
  classical
  by_cases huw : u ≠ w
  · rw [if_pos huw]
    have hpt : ∀ b, addM u w x b
        = (if x = u then (if b = w then 1 else 0) else 0)
          + (if x = w then (if b = u then 1 else 0) else 0) := by
      intro b
      unfold addM
      by_cases hxu : x = u <;> by_cases hxw : x = w
      · exact absurd (hxu.symm.trans hxw) huw
      · rw [if_pos hxu, if_neg hxw]
        by_cases hbw : b = w
        · rw [if_pos ⟨huw, Or.inl ⟨hxu, hbw⟩⟩, if_pos hbw]
        · rw [if_neg (fun h => by
            rcases h.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · exact hbw h2
            · exact huw (hxu.symm.trans h1)), if_neg hbw]
      · rw [if_neg hxu, if_pos hxw]
        by_cases hbu : b = u
        · rw [if_pos ⟨huw, Or.inr ⟨hxw, hbu⟩⟩, if_pos hbu]
        · rw [if_neg (fun h => by
            rcases h.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · exact hxu h1
            · exact hbu h2), if_neg hbu]
      · rw [if_neg hxu, if_neg hxw]
        rw [if_neg (fun h => by
          rcases h.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact hxu h1
          · exact hxw h1)]
    rw [Finset.sum_congr rfl (fun b _ => hpt b), Finset.sum_add_distrib]
    congr 1
    · by_cases hxu : x = u
      · rw [if_pos hxu,
          Finset.sum_congr rfl (fun b (_ : b ∈ Finset.univ) => if_pos hxu),
          Finset.sum_ite_eq' Finset.univ w (fun _ => (1:ℕ)),
          if_pos (Finset.mem_univ w)]
      · rw [if_neg hxu, Finset.sum_eq_zero (fun b _ => if_neg hxu)]
    · by_cases hxw : x = w
      · rw [if_pos hxw,
          Finset.sum_congr rfl (fun b (_ : b ∈ Finset.univ) => if_pos hxw),
          Finset.sum_ite_eq' Finset.univ u (fun _ => (1:ℕ)),
          if_pos (Finset.mem_univ u)]
      · rw [if_neg hxw, Finset.sum_eq_zero (fun b _ => if_neg hxw)]
  · rw [if_neg huw]
    apply Finset.sum_eq_zero
    intro b _
    unfold addM
    rw [if_neg (fun h => huw h.1)]

/-- Row sums of the removed mass. -/
lemma subM_row (x : Fin n) : ∑ b, subM v u w x b
    = (if x = v then 2 else 0) + ((if x = u then 1 else 0) + (if x = w then 1 else 0)) := by
  classical
  unfold subM
  rw [Finset.sum_add_distrib]
  congr 1
  · by_cases hxv : x = v
    · rw [if_pos hxv]
      rw [Finset.sum_congr rfl (fun b (_ : b ∈ Finset.univ) => if_pos hxv)]
      rw [Finset.sum_add_distrib,
        Finset.sum_ite_eq' Finset.univ u (fun _ => (1:ℕ)),
        Finset.sum_ite_eq' Finset.univ w (fun _ => (1:ℕ)),
        if_pos (Finset.mem_univ u), if_pos (Finset.mem_univ w)]
    · rw [if_neg hxv, Finset.sum_eq_zero (fun b _ => if_neg hxv)]
  · rw [Finset.sum_ite_eq' Finset.univ v
      (fun _ => (if x = u then 1 else 0) + (if x = w then 1 else 0)),
      if_pos (Finset.mem_univ v)]

/-! #### Degree accounting -/

lemma splitH_mdeg (hsym : ∀ a b, H a b = H b a)
    (hvu : u ≠ v) (hvw : w ≠ v)
    (hau : 1 ≤ H v u) (haw : 1 ≤ H v w) (hauw : u = w → 2 ≤ H v u) (x : Fin n) :
    mdeg (splitH H v u w) x + ∑ b, subM v u w x b
      = mdeg H x + ∑ b, addM u w x b := by
  unfold mdeg
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun b _ => splitH_add hsym hvu hvw hau haw hauw x b)

lemma splitH_mdeg_v (hsym : ∀ a b, H a b = H b a)
    (hvu : u ≠ v) (hvw : w ≠ v)
    (hau : 1 ≤ H v u) (haw : 1 ≤ H v w) (hauw : u = w → 2 ≤ H v u) :
    mdeg (splitH H v u w) v + 2 = mdeg H v := by
  have h := splitH_mdeg hsym hvu hvw hau haw hauw v
  rw [addM_row, subM_row, if_pos (rfl : (v : Fin n) = v),
    if_neg (fun hh : (v : Fin n) = u => hvu hh.symm),
    if_neg (fun hh : (v : Fin n) = w => hvw hh.symm)] at h
  by_cases huw : u ≠ w
  · rw [if_pos huw] at h
    omega
  · rw [if_neg huw] at h
    omega

lemma splitH_mdeg_other (hsym : ∀ a b, H a b = H b a)
    (hvu : u ≠ v) (hvw : w ≠ v)
    (hau : 1 ≤ H v u) (haw : 1 ≤ H v w) (hauw : u = w → 2 ≤ H v u)
    (x : Fin n) (hxv : x ≠ v) (hx : u ≠ w ∨ x ≠ u) :
    mdeg (splitH H v u w) x = mdeg H x := by
  have h := splitH_mdeg hsym hvu hvw hau haw hauw x
  rw [addM_row, subM_row, if_neg hxv] at h
  by_cases huw : u ≠ w
  · rw [if_pos huw] at h
    omega
  · push_neg at huw
    have hxu : ¬ x = u := by
      rcases hx with h' | h'
      · exact absurd huw h'
      · exact h'
    have hxw : ¬ x = w := fun hh => hxu (hh.trans huw.symm)
    rw [if_neg (fun hh : ¬ (u = w) => hh huw)] at h
    simp only [if_neg hxu, if_neg hxw] at h
    omega

lemma splitH_mdeg_uu (hsym : ∀ a b, H a b = H b a)
    (hvu : u ≠ v) (hvw : w ≠ v)
    (hau : 1 ≤ H v u) (haw : 1 ≤ H v w) (hauw : u = w → 2 ≤ H v u)
    (huw : u = w) :
    mdeg (splitH H v u w) u + 2 = mdeg H u := by
  have h := splitH_mdeg hsym hvu hvw hau haw hauw u
  rw [addM_row, subM_row, if_neg hvu, if_neg (fun hh : ¬ (u = w) => hh huw),
    if_pos rfl, if_pos huw] at h
  omega

/-! #### Cut accounting -/

lemma splitH_mcross (hsym : ∀ a b, H a b = H b a)
    (hvu : u ≠ v) (hvw : w ≠ v)
    (hau : 1 ≤ H v u) (haw : 1 ≤ H v w) (hauw : u = w → 2 ≤ H v u)
    (A B : Finset (Fin n)) :
    mcross (splitH H v u w) A B + mcross (subM v u w) A B
      = mcross H A B + mcross (addM u w) A B := by
  unfold mcross
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun b _ => splitH_add hsym hvu hvw hau haw hauw a b)

lemma crossSub_eval (hvu : u ≠ v) (hvw : w ≠ v) {S : Finset (Fin n)} (hvS : v ∉ S) :
    mcross (subM v u w) S Sᶜ
      = (if u ∈ S then 1 else 0) + (if w ∈ S then 1 else 0) := by
  classical
  unfold mcross subM
  have hpt : ∀ a ∈ S, ∀ b ∈ Sᶜ,
      ((if a = v then (if b = u then 1 else 0) + (if b = w then 1 else 0) else 0)
        + (if b = v then (if a = u then 1 else 0) + (if a = w then 1 else 0) else 0))
      = (if b = v then (if a = u then (1:ℕ) else 0) + (if a = w then 1 else 0) else 0) := by
    intro a ha b _
    rw [if_neg (fun hh : a = v => hvS (hh ▸ ha))]
    exact zero_add _
  rw [Finset.sum_congr rfl (fun a ha =>
    Finset.sum_congr rfl (fun b hb => hpt a ha b hb))]
  have hin : ∀ a ∈ S,
      ∑ b ∈ Sᶜ, (if b = v then (if a = u then (1:ℕ) else 0) + (if a = w then 1 else 0) else 0)
      = (if a = u then 1 else 0) + (if a = w then 1 else 0) := by
    intro a _
    rw [Finset.sum_ite_eq' Sᶜ v
      (fun _ => (if a = u then (1:ℕ) else 0) + (if a = w then 1 else 0)),
      if_pos (Finset.mem_compl.mpr hvS)]
  rw [Finset.sum_congr rfl hin, Finset.sum_add_distrib,
    Finset.sum_ite_eq' S u (fun _ => (1:ℕ)),
    Finset.sum_ite_eq' S w (fun _ => (1:ℕ))]

lemma crossAdd_eval_uu (huw : u = w) (A B : Finset (Fin n)) :
    mcross (addM u w) A B = 0 := by
  unfold mcross addM
  exact Finset.sum_eq_zero (fun a _ => Finset.sum_eq_zero (fun b _ => by
    rw [if_neg (fun hh => hh.1 huw)]))

lemma addM_eval (huw : u ≠ w) (a b : Fin n) :
    addM u w a b
      = (if a = u then (if b = w then 1 else 0) else 0)
        + (if a = w then (if b = u then 1 else 0) else 0) := by
  unfold addM
  by_cases hau : a = u <;> by_cases haw : a = w
  · exact absurd (hau.symm.trans haw) huw
  · rw [if_pos hau, if_neg haw]
    by_cases hbw : b = w
    · rw [if_pos ⟨huw, Or.inl ⟨hau, hbw⟩⟩, if_pos hbw]
    · rw [if_neg (fun hh => by
        rcases hh.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact hbw h2
        · exact haw h1), if_neg hbw]
  · rw [if_neg hau, if_pos haw]
    by_cases hbu : b = u
    · rw [if_pos ⟨huw, Or.inr ⟨haw, hbu⟩⟩, if_pos hbu]
    · rw [if_neg (fun hh => by
        rcases hh.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact hau h1
        · exact hbu h2), if_neg hbu]
  · rw [if_neg hau, if_neg haw,
      if_neg (fun hh : u ≠ w ∧ ((a = u ∧ b = w) ∨ (a = w ∧ b = u)) => by
        rcases hh.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact hau h1
        · exact haw h1)]

lemma crossAdd_eval (huw : u ≠ w) (S : Finset (Fin n)) :
    mcross (addM u w) S Sᶜ
      = (if u ∈ S then (if w ∈ Sᶜ then 1 else 0) else 0)
        + (if w ∈ S then (if u ∈ Sᶜ then 1 else 0) else 0) := by
  classical
  unfold mcross
  rw [Finset.sum_congr rfl (fun a (_ : a ∈ S) =>
    Finset.sum_congr rfl (fun b (_ : b ∈ Sᶜ) => addM_eval huw a b))]
  have h1 : ∀ a ∈ S,
      ∑ b ∈ Sᶜ, ((if a = u then (if b = w then (1:ℕ) else 0) else 0)
        + (if a = w then (if b = u then 1 else 0) else 0))
      = (if a = u then (if w ∈ Sᶜ then 1 else 0) else 0)
        + (if a = w then (if u ∈ Sᶜ then 1 else 0) else 0) := by
    intro a _
    rw [Finset.sum_add_distrib]
    congr 1
    · by_cases hau : a = u
      · rw [if_pos hau, Finset.sum_congr rfl (fun b (_ : b ∈ Sᶜ) => if_pos hau),
          Finset.sum_ite_eq' Sᶜ w (fun _ => (1:ℕ))]
      · rw [if_neg hau, Finset.sum_congr rfl (fun b (_ : b ∈ Sᶜ) => if_neg hau),
          Finset.sum_const_zero]
    · by_cases haw : a = w
      · rw [if_pos haw, Finset.sum_congr rfl (fun b (_ : b ∈ Sᶜ) => if_pos haw),
          Finset.sum_ite_eq' Sᶜ u (fun _ => (1:ℕ))]
      · rw [if_neg haw, Finset.sum_congr rfl (fun b (_ : b ∈ Sᶜ) => if_neg haw),
          Finset.sum_const_zero]
  rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib,
    Finset.sum_ite_eq' S u (fun _ => if w ∈ Sᶜ then (1:ℕ) else 0),
    Finset.sum_ite_eq' S w (fun _ => if u ∈ Sᶜ then (1:ℕ) else 0)]

lemma splitH_mcut_both (hsym : ∀ a b, H a b = H b a)
    (hvu : u ≠ v) (hvw : w ≠ v)
    (hau : 1 ≤ H v u) (haw : 1 ≤ H v w) (hauw : u = w → 2 ≤ H v u)
    {S : Finset (Fin n)} (hvS : v ∉ S) (huS : u ∈ S) (hwS : w ∈ S) :
    mcut (splitH H v u w) S + 2 = mcut H S := by
  have h := splitH_mcross hsym hvu hvw hau haw hauw S Sᶜ
  rw [crossSub_eval hvu hvw hvS] at h
  by_cases huw : u = w
  · rw [crossAdd_eval_uu huw] at h
    simp only [if_pos huS, if_pos hwS] at h
    unfold mcut
    omega
  · rw [crossAdd_eval huw S] at h
    simp only [if_pos huS, if_pos hwS,
      if_neg (fun hh : w ∈ Sᶜ => Finset.mem_compl.mp hh hwS),
      if_neg (fun hh : u ∈ Sᶜ => Finset.mem_compl.mp hh huS)] at h
    unfold mcut
    omega

lemma splitH_mcut_notboth (hsym : ∀ a b, H a b = H b a)
    (hvu : u ≠ v) (hvw : w ≠ v)
    (hau : 1 ≤ H v u) (haw : 1 ≤ H v w) (hauw : u = w → 2 ≤ H v u)
    {S : Finset (Fin n)} (hvS : v ∉ S) (h1 : u ∉ S ∨ w ∉ S) :
    mcut (splitH H v u w) S = mcut H S := by
  have h := splitH_mcross hsym hvu hvw hau haw hauw S Sᶜ
  rw [crossSub_eval hvu hvw hvS] at h
  by_cases huw : u = w
  · rw [crossAdd_eval_uu huw] at h
    have huS : u ∉ S := by
      rcases h1 with h' | h'
      · exact h'
      · rw [huw]; exact h'
    have hwS : w ∉ S := by rw [← huw]; exact huS
    simp only [if_neg huS, if_neg hwS] at h
    unfold mcut
    omega
  · rw [crossAdd_eval huw S] at h
    by_cases huS : u ∈ S <;> by_cases hwS : w ∈ S
    · exfalso
      rcases h1 with h' | h'
      · exact h' huS
      · exact h' hwS
    · simp only [if_pos huS, if_neg hwS, if_pos (Finset.mem_compl.mpr hwS),
        if_neg (fun hh : u ∈ Sᶜ => Finset.mem_compl.mp hh huS)] at h
      unfold mcut
      omega
    · simp only [if_neg huS, if_pos hwS, if_pos (Finset.mem_compl.mpr huS),
        if_neg (fun hh : w ∈ Sᶜ => Finset.mem_compl.mp hh hwS)] at h
      unfold mcut
      omega
    · simp only [if_neg huS, if_neg hwS] at h
      unfold mcut
      omega

/-! #### Cost accounting -/

lemma row_cost_eval (c : Fin n → Fin n → ℝ) (W : Fin n → ℕ) (x : Fin n) :
    ∑ a, ∑ b, (((if a = x then W b else 0 : ℕ)) : ℝ) * c a b
      = ∑ b, (W b : ℝ) * c x b := by
  classical
  rw [Finset.sum_eq_single x]
  · exact Finset.sum_congr rfl (fun b _ => by rw [if_pos rfl])
  · intro a _ hax
    exact Finset.sum_eq_zero (fun b _ => by
      rw [if_neg hax]
      push_cast
      ring)
  · intro hx
    exact absurd (Finset.mem_univ x) hx

lemma col_cost_eval (c : Fin n → Fin n → ℝ) (W : Fin n → ℕ) (x : Fin n) :
    ∑ a, ∑ b, (((if b = x then W a else 0 : ℕ)) : ℝ) * c a b
      = ∑ a, (W a : ℝ) * c a x := by
  classical
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.sum_eq_single x]
  · rw [if_pos rfl]
  · intro b _ hbx
    rw [if_neg hbx]
    push_cast
    ring
  · intro hx
    exact absurd (Finset.mem_univ x) hx

lemma pair_row_eval (c : Fin n → Fin n → ℝ) (x : Fin n) :
    ∑ b, (((if b = u then 1 else 0) + (if b = w then 1 else 0) : ℕ) : ℝ) * c x b
      = c x u + c x w := by
  classical
  have hpt : ∀ b : Fin n,
      (((if b = u then 1 else 0) + (if b = w then 1 else 0) : ℕ) : ℝ) * c x b
      = (if b = u then c x b else 0) + (if b = w then c x b else 0) := by
    intro b
    split_ifs <;> push_cast <;> ring
  rw [Finset.sum_congr rfl (fun b _ => hpt b), Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ u (fun b => c x b),
    Finset.sum_ite_eq' Finset.univ w (fun b => c x b),
    if_pos (Finset.mem_univ u), if_pos (Finset.mem_univ w)]

lemma pair_col_eval (c : Fin n → Fin n → ℝ) (x : Fin n) :
    ∑ a, (((if a = u then 1 else 0) + (if a = w then 1 else 0) : ℕ) : ℝ) * c a x
      = c u x + c w x := by
  classical
  have hpt : ∀ a : Fin n,
      (((if a = u then 1 else 0) + (if a = w then 1 else 0) : ℕ) : ℝ) * c a x
      = (if a = u then c a x else 0) + (if a = w then c a x else 0) := by
    intro a
    split_ifs <;> push_cast <;> ring
  rw [Finset.sum_congr rfl (fun a _ => hpt a), Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ u (fun a => c a x),
    Finset.sum_ite_eq' Finset.univ w (fun a => c a x),
    if_pos (Finset.mem_univ u), if_pos (Finset.mem_univ w)]

lemma subM_cost (c : Fin n → Fin n → ℝ) :
    ∑ a, ∑ b, (subM v u w a b : ℝ) * c a b
      = (c v u + c v w) + (c u v + c w v) := by
  classical
  have hpt : ∀ a b : Fin n, (subM v u w a b : ℝ) * c a b
      = (((if a = v then ((if b = u then 1 else 0) + (if b = w then 1 else 0)) else 0 : ℕ)) : ℝ) * c a b
        + (((if b = v then ((if a = u then 1 else 0) + (if a = w then 1 else 0)) else 0 : ℕ)) : ℝ) * c a b := by
    intro a b
    unfold subM
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => hpt a b))]
  rw [Finset.sum_congr rfl (fun a (_ : a ∈ Finset.univ) => Finset.sum_add_distrib),
    Finset.sum_add_distrib, row_cost_eval c _ v, col_cost_eval c _ v,
    pair_row_eval c v, pair_col_eval c v]

lemma addM_cost_uu (c : Fin n → Fin n → ℝ) (huw : u = w) :
    ∑ a, ∑ b, (addM u w a b : ℝ) * c a b = 0 := by
  refine Finset.sum_eq_zero (fun a _ => Finset.sum_eq_zero (fun b _ => ?_))
  unfold addM
  rw [if_neg (fun hh => hh.1 huw)]
  push_cast
  ring

lemma addM_cost_ne (c : Fin n → Fin n → ℝ) (huw : u ≠ w) :
    ∑ a, ∑ b, (addM u w a b : ℝ) * c a b = c u w + c w u := by
  classical
  have hpt : ∀ a b : Fin n, (addM u w a b : ℝ) * c a b
      = (((if a = u then (if b = w then 1 else 0) else 0 : ℕ)) : ℝ) * c a b
        + (((if a = w then (if b = u then 1 else 0) else 0 : ℕ)) : ℝ) * c a b := by
    intro a b
    rw [addM_eval huw]
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => hpt a b))]
  rw [Finset.sum_congr rfl (fun a (_ : a ∈ Finset.univ) => Finset.sum_add_distrib),
    Finset.sum_add_distrib, row_cost_eval c _ u, row_cost_eval c _ w]
  have h1 : ∑ b, (((if b = w then 1 else 0 : ℕ)) : ℝ) * c u b = c u w := by
    have hpt2 : ∀ b : Fin n, (((if b = w then 1 else 0 : ℕ)) : ℝ) * c u b
        = if b = w then c u b else 0 := by
      intro b
      by_cases hbw : b = w <;> simp [hbw]
    rw [Finset.sum_congr rfl (fun b _ => hpt2 b),
      Finset.sum_ite_eq' Finset.univ w (fun b => c u b), if_pos (Finset.mem_univ w)]
  have h2 : ∑ b, (((if b = u then 1 else 0 : ℕ)) : ℝ) * c w b = c w u := by
    have hpt2 : ∀ b : Fin n, (((if b = u then 1 else 0 : ℕ)) : ℝ) * c w b
        = if b = u then c w b else 0 := by
      intro b
      by_cases hbu : b = u <;> simp [hbu]
    rw [Finset.sum_congr rfl (fun b _ => hpt2 b),
      Finset.sum_ite_eq' Finset.univ u (fun b => c w b), if_pos (Finset.mem_univ u)]
  rw [h1, h2]

/-- The split does not increase the total cost, for a metric cost. -/
lemma splitH_cost (c : Fin n → Fin n → ℝ)
    (hcs : ∀ a b, c a b = c b a) (hcn : ∀ a b, 0 ≤ c a b)
    (hct : ∀ a b d, c a d ≤ c a b + c b d)
    (hsym : ∀ a b, H a b = H b a)
    (hvu : u ≠ v) (hvw : w ≠ v)
    (hau : 1 ≤ H v u) (haw : 1 ≤ H v w) (hauw : u = w → 2 ≤ H v u) :
    ∑ a, ∑ b, ((splitH H v u w) a b : ℝ) * c a b
      ≤ ∑ a, ∑ b, (H a b : ℝ) * c a b := by
  classical
  have key : ∀ a b : Fin n, ((splitH H v u w) a b : ℝ) * c a b
      = (H a b : ℝ) * c a b + (addM u w a b : ℝ) * c a b
        - (subM v u w a b : ℝ) * c a b := by
    intro a b
    have h := splitH_add hsym hvu hvw hau haw hauw a b
    have h2 : ((splitH H v u w) a b : ℝ) + (subM v u w a b : ℝ)
        = (H a b : ℝ) + (addM u w a b : ℝ) := by
      exact_mod_cast congrArg (fun t : ℕ => (t : ℝ)) h
    have h3 : ((splitH H v u w) a b : ℝ)
        = (H a b : ℝ) + (addM u w a b : ℝ) - (subM v u w a b : ℝ) := by
      linarith
    rw [h3]
    ring
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => key a b))]
  have hInner : ∀ a : Fin n,
      ∑ b, ((H a b : ℝ) * c a b + (addM u w a b : ℝ) * c a b
        - (subM v u w a b : ℝ) * c a b)
      = ∑ b, (H a b : ℝ) * c a b + ∑ b, (addM u w a b : ℝ) * c a b
        - ∑ b, (subM v u w a b : ℝ) * c a b := by
    intro a
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [Finset.sum_congr rfl (fun a (_ : a ∈ Finset.univ) => hInner a),
    Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hsub := subM_cost (v := v) (u := u) (w := w) c
  by_cases huw : u = w
  · rw [addM_cost_uu c huw, hsub]
    have h1 := hcn v u
    have h2 := hcn v w
    have h3 := hcn u v
    have h4 := hcn w v
    linarith
  · rw [addM_cost_ne c huw, hsub]
    have h1 : c u w ≤ c u v + c v w := hct u v w
    have h2 : c w u ≤ c w v + c v u := hct w v u
    linarith

end SplitFacts

/-! ### Parity and insertion identities for cuts -/

section CutFacts

variable {H : Fin n → Fin n → ℕ} {v : Fin n}

lemma even_sum_of_even {f : Fin n → ℕ} :
    ∀ s : Finset (Fin n), (∀ x ∈ s, Even (f x)) → Even (∑ x ∈ s, f x) := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty => exact fun _ => ⟨0, by simp⟩
  | @insert x s hx ih =>
    intro h
    rw [Finset.sum_insert hx]
    obtain ⟨a, ha⟩ := h x (Finset.mem_insert_self x s)
    obtain ⟨b, hb⟩ := ih (fun y hy => h y (Finset.mem_insert_of_mem hy))
    exact ⟨a + b, by omega⟩

lemma inner_even (hsym : ∀ a b, H a b = H b a) (hdiag : ∀ a, H a a = 0) :
    ∀ S : Finset (Fin n), Even (∑ a ∈ S, ∑ b ∈ S, H a b) := by
  classical
  intro S
  induction S using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert x s hx ih =>
    obtain ⟨k, hk⟩ := ih
    have h1 : ∀ a ∈ s, ∑ b ∈ insert x s, H a b = H a x + ∑ b ∈ s, H a b :=
      fun a _ => Finset.sum_insert hx
    rw [Finset.sum_insert hx, Finset.sum_insert hx,
      Finset.sum_congr rfl h1, Finset.sum_add_distrib, hdiag x,
      Finset.sum_congr rfl (fun a (_ : a ∈ s) => hsym a x)]
    refine ⟨∑ b ∈ s, H x b + k, ?_⟩
    have he : s.sum (H x) = ∑ b ∈ s, H x b := rfl
    omega

lemma mcut_add_inner (S : Finset (Fin n)) :
    mcut H S + ∑ a ∈ S, ∑ b ∈ S, H a b = ∑ a ∈ S, mdeg H a := by
  unfold mcut mcross mdeg
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [add_comm]
  exact Finset.sum_add_sum_compl S (fun b => H a b)

lemma mcut_even (hsym : ∀ a b, H a b = H b a) (hdiag : ∀ a, H a a = 0)
    (heven : ∀ x, Even (mdeg H x)) (S : Finset (Fin n)) :
    Even (mcut H S) := by
  have h1 := mcut_add_inner (H := H) S
  obtain ⟨k, hk⟩ := inner_even hsym hdiag S
  obtain ⟨m, hm⟩ := even_sum_of_even (f := mdeg H) S (fun x _ => heven x)
  exact ⟨m - k, by omega⟩

lemma mcut_singleton (hdiag : ∀ a, H a a = 0) (x : Fin n) :
    mcut H {x} = mdeg H x := by
  have h := mcut_add_inner (H := H) {x}
  rw [Finset.sum_singleton, Finset.sum_singleton, Finset.sum_singleton,
    hdiag x] at h
  omega

lemma mcut_insert (hsym : ∀ a b, H a b = H b a) (hdiag : ∀ a, H a a = 0)
    {X : Finset (Fin n)} (hv : v ∉ X) :
    mcut H (insert v X) + ∑ b ∈ X, H v b = mcut H X + ∑ b ∈ Xᶜ, H v b := by
  unfold mcut mcross
  rw [Finset.compl_insert, Finset.sum_insert hv]
  have h1 : ∑ b ∈ Xᶜ.erase v, H v b + H v v = ∑ b ∈ Xᶜ, H v b :=
    Finset.sum_erase_add _ _ (Finset.mem_compl.mpr hv)
  have h2 : ∑ a ∈ X, ∑ b ∈ Xᶜ.erase v, H a b + ∑ a ∈ X, H a v
      = ∑ a ∈ X, ∑ b ∈ Xᶜ, H a b := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl
      (fun a _ => Finset.sum_erase_add _ _ (Finset.mem_compl.mpr hv))
  have h3 : ∑ a ∈ X, H a v = ∑ a ∈ X, H v a :=
    Finset.sum_congr rfl (fun a _ => hsym a v)
  have h4 : H v v = 0 := hdiag v
  omega

lemma mcross_single_le {A B : Finset (Fin n)} {a b : Fin n}
    (ha : a ∈ A) (hb : b ∈ B) : H a b ≤ mcross H A B := by
  unfold mcross
  calc H a b ≤ ∑ y ∈ B, H a y :=
        Finset.single_le_sum (fun y _ => Nat.zero_le _) hb
    _ ≤ ∑ x ∈ A, ∑ y ∈ B, H x y :=
        Finset.single_le_sum (f := fun x => ∑ y ∈ B, H x y)
          (fun x _ => Nat.zero_le _) ha

/-- A `T`-separating superset that inserts a non-terminal is still separating. -/
lemma TSep_insert {T S : Finset (Fin n)} (hvT : v ∉ T) (h : TSep T S) :
    TSep T (insert v S) := by
  obtain ⟨h1, h2⟩ := h
  constructor
  · rw [Finset.insert_inter_of_notMem hvT]
    exact h1
  · rw [Finset.compl_insert]
    obtain ⟨x, hx⟩ := h2
    obtain ⟨hx1, hx2⟩ := Finset.mem_inter.mp hx
    exact ⟨x, Finset.mem_inter.mpr
      ⟨Finset.mem_erase.mpr ⟨fun hh => hvT (hh ▸ hx2), hx1⟩, hx2⟩⟩

end CutFacts

/-! ### Existence of an admissible splitting pair (Lovász) -/

section Admissible

variable {H : Fin n → Fin n → ℕ} {v : Fin n}

lemma exists_admissible (T : Finset (Fin n)) (hT2 : 2 ≤ T.card)
    (N : ℕ)
    (hsym : ∀ a b, H a b = H b a) (hdiag : ∀ a, H a a = 0)
    (heven : ∀ x, Even (mdeg H x))
    (hdegT : ∀ t ∈ T, mdeg H t = 2 * N)
    (hcut : ∀ S, TSep T S → 2 * N ≤ mcut H S)
    (hvT : v ∉ T) (hvpos : mdeg H v ≠ 0) :
    ∃ p q : Fin n, p ≠ v ∧ q ≠ v ∧ 1 ≤ H v p ∧ 1 ≤ H v q ∧
      (p = q → 2 ≤ H v p ∧ p ∉ T) ∧
      (∀ S, TSep T S → v ∉ S → p ∈ S → q ∈ S → 2 * N + 2 ≤ mcut H S) := by
  classical
  -- v has a neighbour
  have hex : ∃ b, H v b ≠ 0 := by
    by_contra hno
    push_neg at hno
    exact hvpos (Finset.sum_eq_zero (fun b _ => hno b))
  obtain ⟨u₀, hu₀⟩ := hex
  have hu₀v : u₀ ≠ v := fun h => hu₀ (by rw [h]; exact hdiag v)
  have hmdeg2 : 2 ≤ mdeg H v := by
    obtain ⟨r, hr⟩ := heven v
    have h1 : H v u₀ ≤ mdeg H v :=
      Finset.single_le_sum (fun b _ => Nat.zero_le _) (Finset.mem_univ u₀)
    have h2 : 1 ≤ H v u₀ := Nat.one_le_iff_ne_zero.mpr hu₀
    omega
  by_cases hsingle : ∀ b, H v b ≠ 0 → b = u₀
  · -- single distinct neighbour: the deletion pair (u₀, u₀) is admissible
    have hall : H v u₀ = mdeg H v := by
      unfold mdeg
      rw [Finset.sum_eq_single u₀]
      · intro b _ hb
        by_contra h0
        exact hb (hsingle b h0)
      · intro h
        exact absurd (Finset.mem_univ u₀) h
    have hu₀T : u₀ ∉ T := by
      intro huT
      obtain ⟨t, htT, htu⟩ := Finset.exists_mem_ne (s := T) (by omega) u₀
      have htv : t ≠ v := fun h => hvT (h ▸ htT)
      have hvs : v ∉ ({u₀} : Finset (Fin n)) := fun h =>
        hu₀v ((Finset.mem_singleton.mp h).symm)
      have hTS : TSep T (insert v {u₀}) := by
        constructor
        · exact ⟨u₀, Finset.mem_inter.mpr
            ⟨Finset.mem_insert_of_mem (Finset.mem_singleton_self u₀), huT⟩⟩
        · refine ⟨t, Finset.mem_inter.mpr ⟨?_, htT⟩⟩
          rw [Finset.mem_compl]
          intro hmem
          rcases Finset.mem_insert.mp hmem with h | h
          · exact htv h
          · exact htu (Finset.mem_singleton.mp h)
      have hc1 := hcut _ hTS
      have hins := mcut_insert hsym hdiag hvs
      rw [Finset.sum_singleton] at hins
      have hzero : ∑ b ∈ ({u₀} : Finset (Fin n))ᶜ, H v b = 0 := by
        refine Finset.sum_eq_zero (fun b hb => ?_)
        by_contra h0
        exact (Finset.mem_compl.mp hb) (Finset.mem_singleton.mpr (hsingle b h0))
      have hsing : mcut H {u₀} = mdeg H u₀ := mcut_singleton hdiag u₀
      have hdu := hdegT u₀ huT
      omega
    refine ⟨u₀, u₀, hu₀v, hu₀v, Nat.one_le_iff_ne_zero.mpr hu₀,
      Nat.one_le_iff_ne_zero.mpr hu₀, fun _ => ⟨by omega, hu₀T⟩, ?_⟩
    intro S hTS hvS huS _
    have hTS' := TSep_insert hvT hTS
    have hins := mcut_insert hsym hdiag hvS
    have hzero : ∑ b ∈ Sᶜ, H v b = 0 := by
      refine Finset.sum_eq_zero (fun b hb => ?_)
      by_contra h0
      have hb0 : b = u₀ := hsingle b h0
      exact (Finset.mem_compl.mp hb) (hb0 ▸ huS)
    have hsum : ∑ b ∈ S, H v b + ∑ b ∈ Sᶜ, H v b = mdeg H v :=
      Finset.sum_add_sum_compl S (fun b => H v b)
    have hc1 := hcut _ hTS'
    omega
  · -- at least two distinct neighbours
    push_neg at hsingle
    obtain ⟨w₀, hw₀, hw₀u₀⟩ := hsingle
    by_cases hgood : ∃ q, H v q ≠ 0 ∧ q ≠ u₀ ∧
        (∀ S, TSep T S → v ∉ S → u₀ ∈ S → q ∈ S → 2 * N + 2 ≤ mcut H S)
    · obtain ⟨q, h1, h2, h3⟩ := hgood
      exact ⟨u₀, q, hu₀v, fun h => h1 (by rw [h]; exact hdiag v),
        Nat.one_le_iff_ne_zero.mpr hu₀, Nat.one_le_iff_ne_zero.mpr h1,
        fun h => absurd h.symm h2, h3⟩
    · exfalso
      push_neg at hgood
      -- every candidate pair is blocked by a dangerous set
      have hdang : ∀ S, TSep T S → mcut H S < 2 * N + 2 → mcut H S = 2 * N := by
        intro S hTS hlt
        have h1 := hcut S hTS
        obtain ⟨r, hr⟩ := mcut_even hsym hdiag heven S
        omega
      set F := Finset.univ.powerset.filter
        (fun X : Finset (Fin n) =>
          TSep T X ∧ v ∉ X ∧ u₀ ∈ X ∧ mcut H X ≤ 2 * N + 1) with hF
      have hFne : F.Nonempty := by
        obtain ⟨S, hTS, hvS, huS, hwS, hlt⟩ := hgood w₀ hw₀ hw₀u₀
        exact ⟨S, Finset.mem_filter.mpr
          ⟨Finset.mem_powerset.mpr (Finset.subset_univ S),
            hTS, hvS, huS, by omega⟩⟩
      obtain ⟨X, hXF, hXmax⟩ := Finset.exists_max_image F Finset.card hFne
      obtain ⟨-, hXsep, hXv, hXu₀, hXle⟩ := Finset.mem_filter.mp hXF
      have hXcut : mcut H X = 2 * N := hdang X hXsep (by omega)
      -- Claim 1: some neighbour of v lies outside X
      have hout : ∃ b, H v b ≠ 0 ∧ b ∉ X := by
        by_contra hno
        push_neg at hno
        have hzero : ∑ b ∈ Xᶜ, H v b = 0 := by
          refine Finset.sum_eq_zero (fun b hb => ?_)
          by_contra h0
          exact (Finset.mem_compl.mp hb) (hno b h0)
        have hins := mcut_insert hsym hdiag hXv
        have hsum : ∑ b ∈ X, H v b + ∑ b ∈ Xᶜ, H v b = mdeg H v :=
          Finset.sum_add_sum_compl X (fun b => H v b)
        have hTS' := TSep_insert hvT hXsep
        have hc1 := hcut _ hTS'
        omega
      obtain ⟨w₁, hw₁, hw₁X⟩ := hout
      have hw₁u₀ : w₁ ≠ u₀ := fun h => hw₁X (h ▸ hXu₀)
      obtain ⟨Y, hYsep, hYv, hYu₀, hYw₁, hYlt⟩ := hgood w₁ hw₁ hw₁u₀
      have hYcut : mcut H Y = 2 * N := hdang Y hYsep hYlt
      obtain ⟨hIa, hIb⟩ := mcut_submod hsym X Y
      by_cases hβ : ((X ∩ Y) ∩ T = ∅) ∨ (T ⊆ X ∪ Y)
      · -- identity Ib: the difference sets separate T, forcing zero crossing,
        -- contradicting the edge v–u₀
        have hXmY : TSep T (X \ Y) := by
          constructor
          · by_contra hemp
            have hsub : X ∩ T ⊆ Y := by
              intro x hx
              obtain ⟨hx1, hx2⟩ := Finset.mem_inter.mp hx
              by_contra hxY
              exact hemp ⟨x, Finset.mem_inter.mpr
                ⟨Finset.mem_sdiff.mpr ⟨hx1, hxY⟩, hx2⟩⟩
            rcases hβ with hI | hU
            · obtain ⟨x, hx⟩ := hXsep.1
              obtain ⟨hx1, hx2⟩ := Finset.mem_inter.mp hx
              have hxY : x ∈ Y := hsub (Finset.mem_inter.mpr ⟨hx1, hx2⟩)
              have : x ∈ (X ∩ Y) ∩ T := Finset.mem_inter.mpr
                ⟨Finset.mem_inter.mpr ⟨hx1, hxY⟩, hx2⟩
              rw [hI] at this
              exact absurd this (Finset.notMem_empty x)
            · obtain ⟨t, ht⟩ := hYsep.2
              obtain ⟨ht1, ht2⟩ := Finset.mem_inter.mp ht
              have htY : t ∉ Y := Finset.mem_compl.mp ht1
              have htXY : t ∈ X ∪ Y := hU ht2
              have htX : t ∈ X := by
                rcases Finset.mem_union.mp htXY with h | h
                · exact h
                · exact absurd h htY
              exact htY (hsub (Finset.mem_inter.mpr ⟨htX, ht2⟩))
          · obtain ⟨x, hx⟩ := hXsep.2
            obtain ⟨hx1, hx2⟩ := Finset.mem_inter.mp hx
            refine ⟨x, Finset.mem_inter.mpr ⟨?_, hx2⟩⟩
            rw [Finset.mem_compl]
            intro hmem
            exact (Finset.mem_compl.mp hx1) (Finset.mem_sdiff.mp hmem).1
        have hYmX : TSep T (Y \ X) := by
          constructor
          · by_contra hemp
            have hsub : Y ∩ T ⊆ X := by
              intro x hx
              obtain ⟨hx1, hx2⟩ := Finset.mem_inter.mp hx
              by_contra hxX
              exact hemp ⟨x, Finset.mem_inter.mpr
                ⟨Finset.mem_sdiff.mpr ⟨hx1, hxX⟩, hx2⟩⟩
            rcases hβ with hI | hU
            · obtain ⟨x, hx⟩ := hYsep.1
              obtain ⟨hx1, hx2⟩ := Finset.mem_inter.mp hx
              have hxX : x ∈ X := hsub (Finset.mem_inter.mpr ⟨hx1, hx2⟩)
              have : x ∈ (X ∩ Y) ∩ T := Finset.mem_inter.mpr
                ⟨Finset.mem_inter.mpr ⟨hxX, hx1⟩, hx2⟩
              rw [hI] at this
              exact absurd this (Finset.notMem_empty x)
            · obtain ⟨t, ht⟩ := hXsep.2
              obtain ⟨ht1, ht2⟩ := Finset.mem_inter.mp ht
              have htX : t ∉ X := Finset.mem_compl.mp ht1
              have htXY : t ∈ X ∪ Y := hU ht2
              have htY : t ∈ Y := by
                rcases Finset.mem_union.mp htXY with h | h
                · exact absurd h htX
                · exact h
              exact htX (hsub (Finset.mem_inter.mpr ⟨htY, ht2⟩))
          · obtain ⟨x, hx⟩ := hYsep.2
            obtain ⟨hx1, hx2⟩ := Finset.mem_inter.mp hx
            refine ⟨x, Finset.mem_inter.mpr ⟨?_, hx2⟩⟩
            rw [Finset.mem_compl]
            intro hmem
            exact (Finset.mem_compl.mp hx1) (Finset.mem_sdiff.mp hmem).1
        have h1 := hcut _ hXmY
        have h2 := hcut _ hYmX
        have hcr : H u₀ v ≤ mcross H (X ∩ Y) ((X ∪ Y)ᶜ) := by
          refine mcross_single_le (Finset.mem_inter.mpr ⟨hXu₀, hYu₀⟩) ?_
          rw [Finset.mem_compl, Finset.mem_union]
          push_neg
          exact ⟨hXv, hYv⟩
        have hpos : H u₀ v ≠ 0 := by
          rw [hsym u₀ v]
          exact hu₀
        omega
      · -- identity Ia: the union is a strictly larger dangerous set
        push_neg at hβ
        obtain ⟨hIT, hUT⟩ := hβ
        have hUsep : TSep T (X ∪ Y) := by
          constructor
          · obtain ⟨x, hx⟩ := hXsep.1
            obtain ⟨hx1, hx2⟩ := Finset.mem_inter.mp hx
            exact ⟨x, Finset.mem_inter.mpr ⟨Finset.mem_union_left Y hx1, hx2⟩⟩
          · obtain ⟨t, ht1, ht2⟩ := Finset.not_subset.mp hUT
            exact ⟨t, Finset.mem_inter.mpr ⟨Finset.mem_compl.mpr ht2, ht1⟩⟩
        have hIsep : TSep T (X ∩ Y) := by
          constructor
          · exact hIT
          · obtain ⟨x, hx⟩ := hXsep.2
            obtain ⟨hx1, hx2⟩ := Finset.mem_inter.mp hx
            refine ⟨x, Finset.mem_inter.mpr ⟨?_, hx2⟩⟩
            rw [Finset.mem_compl]
            intro hmem
            exact (Finset.mem_compl.mp hx1) (Finset.mem_inter.mp hmem).1
        have h1 := hcut _ hUsep
        have h2 := hcut _ hIsep
        have hUcut : mcut H (X ∪ Y) ≤ 2 * N + 1 := by omega
        have hUv : v ∉ X ∪ Y := by
          rw [Finset.mem_union]
          push_neg
          exact ⟨hXv, hYv⟩
        have hUF : (X ∪ Y) ∈ F := Finset.mem_filter.mpr
          ⟨Finset.mem_powerset.mpr (Finset.subset_univ _),
            hUsep, hUv, Finset.mem_union_left Y hXu₀, hUcut⟩
        have hcard := hXmax _ hUF
        have hlt : X.card < (X ∪ Y).card :=
          Finset.card_lt_card ((Finset.ssubset_iff_of_subset
            Finset.subset_union_left).mpr
            ⟨w₁, Finset.mem_union_right X hYw₁, hw₁X⟩)
        omega

end Admissible

/-! ### Preservation of the invariants under one split -/

section SplitPreserve

variable {H : Fin n → Fin n → ℕ} {v u w : Fin n}

lemma split_preserves (T : Finset (Fin n)) (N : ℕ)
    (hsym : ∀ a b, H a b = H b a)
    (hvu : u ≠ v) (hvw : w ≠ v)
    (hau : 1 ≤ H v u) (haw : 1 ≤ H v w) (hauw : u = w → 2 ≤ H v u)
    (hcut : ∀ S, TSep T S → 2 * N ≤ mcut H S)
    (hadm : ∀ S, TSep T S → v ∉ S → u ∈ S → w ∈ S → 2 * N + 2 ≤ mcut H S) :
    ∀ S, TSep T S → 2 * N ≤ mcut (splitH H v u w) S := by
  have hmain : ∀ S, TSep T S → v ∉ S → 2 * N ≤ mcut (splitH H v u w) S := by
    intro S hTS hvS
    by_cases hb : u ∈ S ∧ w ∈ S
    · have h1 := splitH_mcut_both hsym hvu hvw hau haw hauw hvS hb.1 hb.2
      have h2 := hadm S hTS hvS hb.1 hb.2
      omega
    · have h1 := splitH_mcut_notboth hsym hvu hvw hau haw hauw hvS (by tauto)
      have h2 := hcut S hTS
      omega
  intro S hTS
  by_cases hvS : v ∈ S
  · have h1 := hmain Sᶜ (TSep_compl hTS) (fun h => (Finset.mem_compl.mp h) hvS)
    rw [mcut_compl (fun a b => splitH_symm hsym a b) S] at h1
    exact h1
  · exact hmain S hTS hvS

lemma split_degT (T : Finset (Fin n)) (N : ℕ)
    (hsym : ∀ a b, H a b = H b a)
    (hvu : u ≠ v) (hvw : w ≠ v)
    (hau : 1 ≤ H v u) (haw : 1 ≤ H v w) (hauw : u = w → 2 ≤ H v u)
    (hvT : v ∉ T) (huT : u = w → u ∉ T)
    (hdegT : ∀ t ∈ T, mdeg H t = 2 * N) :
    ∀ t ∈ T, mdeg (splitH H v u w) t = 2 * N := by
  intro t ht
  have htv : t ≠ v := fun h => hvT (h ▸ ht)
  by_cases huw : u = w
  · have htu : t ≠ u := fun h => (huT huw) (h ▸ ht)
    rw [splitH_mdeg_other hsym hvu hvw hau haw hauw t htv (Or.inr htu)]
    exact hdegT t ht
  · rw [splitH_mdeg_other hsym hvu hvw hau haw hauw t htv (Or.inl huw)]
    exact hdegT t ht

lemma split_even
    (hsym : ∀ a b, H a b = H b a)
    (hvu : u ≠ v) (hvw : w ≠ v)
    (hau : 1 ≤ H v u) (haw : 1 ≤ H v w) (hauw : u = w → 2 ≤ H v u)
    (heven : ∀ x, Even (mdeg H x)) :
    ∀ x, Even (mdeg (splitH H v u w) x) := by
  intro x
  by_cases hxv : x = v
  · rw [hxv]
    have h := splitH_mdeg_v hsym hvu hvw hau haw hauw
    obtain ⟨r, hr⟩ := heven v
    exact ⟨r - 1, by omega⟩
  · by_cases huw : u = w
    · by_cases hxu : x = u
      · rw [hxu]
        have h := splitH_mdeg_uu hsym hvu hvw hau haw hauw huw
        obtain ⟨r, hr⟩ := heven u
        exact ⟨r - 1, by omega⟩
      · rw [splitH_mdeg_other hsym hvu hvw hau haw hauw x hxv (Or.inr hxu)]
        exact heven x
    · rw [splitH_mdeg_other hsym hvu hvw hau haw hauw x hxv (Or.inl huw)]
      exact heven x

lemma split_mass (T : Finset (Fin n))
    (hsym : ∀ a b, H a b = H b a)
    (hvu : u ≠ v) (hvw : w ≠ v)
    (hau : 1 ≤ H v u) (haw : 1 ≤ H v w) (hauw : u = w → 2 ≤ H v u)
    (hvTc : v ∈ Tᶜ) :
    ∑ x ∈ Tᶜ, mdeg (splitH H v u w) x + 2 ≤ ∑ x ∈ Tᶜ, mdeg H x := by
  have hv2 := splitH_mdeg_v hsym hvu hvw hau haw hauw
  have hrest : ∀ x ∈ Tᶜ.erase v, mdeg (splitH H v u w) x ≤ mdeg H x := by
    intro x hx
    have hxv : x ≠ v := (Finset.mem_erase.mp hx).1
    by_cases huw : u = w
    · by_cases hxu : x = u
      · have h := splitH_mdeg_uu hsym hvu hvw hau haw hauw huw
        rw [hxu]
        omega
      · exact le_of_eq (splitH_mdeg_other hsym hvu hvw hau haw hauw x hxv (Or.inr hxu))
    · exact le_of_eq (splitH_mdeg_other hsym hvu hvw hau haw hauw x hxv (Or.inl huw))
  have hsum : ∑ x ∈ Tᶜ.erase v, mdeg (splitH H v u w) x
      ≤ ∑ x ∈ Tᶜ.erase v, mdeg H x := Finset.sum_le_sum hrest
  have e1 : mdeg (splitH H v u w) v + ∑ x ∈ Tᶜ.erase v, mdeg (splitH H v u w) x
      = ∑ x ∈ Tᶜ, mdeg (splitH H v u w) x :=
    Finset.add_sum_erase Tᶜ (fun x => mdeg (splitH H v u w) x) hvTc
  have e2 : mdeg H v + ∑ x ∈ Tᶜ.erase v, mdeg H x = ∑ x ∈ Tᶜ, mdeg H x :=
    Finset.add_sum_erase Tᶜ (fun x => mdeg H x) hvTc
  omega

lemma support_of_zero {T : Finset (Fin n)}
    (hsym : ∀ a b, H a b = H b a)
    (hzero : ∀ x ∈ Tᶜ, mdeg H x = 0) :
    ∀ a b, H a b ≠ 0 → a ∈ T ∧ b ∈ T := by
  intro a b hab
  constructor
  · by_contra haT
    have h := hzero a (Finset.mem_compl.mpr haT)
    unfold mdeg at h
    exact hab ((Finset.sum_eq_zero_iff.mp h) b (Finset.mem_univ b))
  · by_contra hbT
    have h := hzero b (Finset.mem_compl.mpr hbT)
    unfold mdeg at h
    have h2 := (Finset.sum_eq_zero_iff.mp h) a (Finset.mem_univ a)
    exact hab (by rw [hsym a b]; exact h2)

end SplitPreserve

/-! ### The elimination induction -/

lemma elim_aux (c : Fin n → Fin n → ℝ)
    (hcs : ∀ a b, c a b = c b a) (hcn : ∀ a b, 0 ≤ c a b)
    (hct : ∀ a b d, c a d ≤ c a b + c b d)
    (T : Finset (Fin n)) (hT2 : 2 ≤ T.card) (N : ℕ) :
    ∀ Φ : ℕ, ∀ H : Fin n → Fin n → ℕ,
      (∀ a b, H a b = H b a) → (∀ a, H a a = 0) →
      (∀ x, Even (mdeg H x)) →
      (∀ t ∈ T, mdeg H t = 2 * N) →
      (∀ S, TSep T S → 2 * N ≤ mcut H S) →
      ∑ x ∈ Tᶜ, mdeg H x ≤ Φ →
      ∃ H' : Fin n → Fin n → ℕ,
        (∀ a b, H' a b = H' b a) ∧ (∀ a, H' a a = 0) ∧
        (∀ a b, H' a b ≠ 0 → a ∈ T ∧ b ∈ T) ∧
        (∀ t ∈ T, mdeg H' t = 2 * N) ∧
        (∀ S, TSep T S → 2 * N ≤ mcut H' S) ∧
        ∑ a, ∑ b, (H' a b : ℝ) * c a b ≤ ∑ a, ∑ b, (H a b : ℝ) * c a b := by
  intro Φ
  induction Φ with
  | zero =>
    intro H hsym hdiag heven hdegT hcut hΦ
    have hz : ∀ x ∈ Tᶜ, mdeg H x = 0 :=
      Finset.sum_eq_zero_iff.mp (Nat.le_zero.mp hΦ)
    exact ⟨H, hsym, hdiag, support_of_zero hsym hz, hdegT, hcut, le_refl _⟩
  | succ Φ ih =>
    intro H hsym hdiag heven hdegT hcut hΦ
    by_cases hz : ∀ x ∈ Tᶜ, mdeg H x = 0
    · exact ⟨H, hsym, hdiag, support_of_zero hsym hz, hdegT, hcut, le_refl _⟩
    · push_neg at hz
      obtain ⟨v, hvTc, hvpos⟩ := hz
      have hvT : v ∉ T := Finset.mem_compl.mp hvTc
      obtain ⟨u, w, huv, hwv, hau, haw, hcase, hadm⟩ :=
        exists_admissible T hT2 N hsym hdiag heven hdegT hcut hvT hvpos
      have hauw : u = w → 2 ≤ H v u := fun h => (hcase h).1
      have huT : u = w → u ∉ T := fun h => (hcase h).2
      have hsym2 : ∀ a b, splitH H v u w a b = splitH H v u w b a :=
        fun a b => splitH_symm hsym a b
      have hdiag2 : ∀ a, splitH H v u w a a = 0 :=
        fun a => splitH_diag hdiag a
      have heven2 := split_even hsym huv hwv hau haw hauw heven
      have hdegT2 := split_degT T N hsym huv hwv hau haw hauw hvT huT hdegT
      have hcut2 := split_preserves T N hsym huv hwv hau haw hauw hcut hadm
      have hmass := split_mass T hsym huv hwv hau haw hauw hvTc
      obtain ⟨H', p1, p2, p3, p4, p5, p6⟩ :=
        ih (splitH H v u w) hsym2 hdiag2 heven2 hdegT2 hcut2 (by omega)
      exact ⟨H', p1, p2, p3, p4, p5,
        le_trans p6 (splitH_cost c hcs hcn hct hsym huv hwv hau haw hauw)⟩

/-- Lovász splitting-off, metric form: all Steiner vertices of a `2N`-regular
even multigraph can be split off, preserving terminal cuts and degrees and
not increasing the metric cost. -/
theorem eliminate_steiner2_thm (c : Fin n → Fin n → ℝ) (hc : IsMetricCost c)
    (T : Finset (Fin n)) (hT2 : 2 ≤ T.card) (N : ℕ)
    (H : Fin n → Fin n → ℕ) (hsym : ∀ u v, H u v = H v u) (hdiag : ∀ v, H v v = 0)
    (hdeg : ∀ v, ∑ u, H v u = 2 * N)
    (hcut : ∀ S : Finset (Fin n), (S ∩ T).Nonempty → (Sᶜ ∩ T).Nonempty →
      2 * N ≤ ∑ u ∈ S, ∑ v ∈ Sᶜ, H u v) :
    ∃ H' : Fin n → Fin n → ℕ, (∀ u v, H' u v = H' v u) ∧ (∀ v, H' v v = 0) ∧
      (∀ u v, H' u v ≠ 0 → u ∈ T ∧ v ∈ T) ∧
      (∀ v ∈ T, ∑ u, H' v u = 2 * N) ∧
      (∀ S : Finset (Fin n), (S ∩ T).Nonempty → (Sᶜ ∩ T).Nonempty →
        2 * N ≤ ∑ u ∈ S, ∑ v ∈ Sᶜ, H' u v) ∧
      ∑ u, ∑ v, (H' u v : ℝ) * c u v ≤ ∑ u, ∑ v, (H u v : ℝ) * c u v := by
  obtain ⟨hcs, hcd, hct⟩ := hc
  have hcn : ∀ a b, 0 ≤ c a b := by
    intro a b
    have h1 := hct a b a
    rw [hcd a, hcs b a] at h1
    linarith
  have heven : ∀ x, Even (mdeg H x) := by
    intro x
    refine ⟨N, ?_⟩
    have h := hdeg x
    unfold mdeg
    omega
  have hdegT : ∀ t ∈ T, mdeg H t = 2 * N := by
    intro t _
    have h := hdeg t
    unfold mdeg
    omega
  have hcut' : ∀ S, TSep T S → 2 * N ≤ mcut H S := by
    intro S hS
    have h := hcut S hS.1 hS.2
    unfold mcut mcross
    omega
  obtain ⟨H', p1, p2, p3, p4, p5, p6⟩ :=
    elim_aux c hcs hcn hct T hT2 N (∑ x ∈ Tᶜ, mdeg H x) H hsym hdiag
      heven hdegT hcut' (le_refl _)
  refine ⟨H', p1, p2, p3, p4, ?_, p6⟩
  intro S h1 h2
  have h := p5 S ⟨h1, h2⟩
  unfold mcut mcross at h
  exact h

end MetricTSP

open MetricTSP

theorem solution (n : ℕ) (c : Fin n → Fin n → ℝ) (hc : IsMetricCost c)
    (T : Finset (Fin n)) (hT2 : 2 ≤ T.card) (N : ℕ) (hN : 1 ≤ N)
    (H : Fin n → Fin n → ℕ) (hsym : ∀ u v, H u v = H v u) (hdiag : ∀ v, H v v = 0)
    (hdeg : ∀ v, ∑ u, H v u = 2 * N)
    (hcut : ∀ S : Finset (Fin n), (S ∩ T).Nonempty → (Sᶜ ∩ T).Nonempty →
      2 * N ≤ ∑ u ∈ S, ∑ v ∈ Sᶜ, H u v) :
    ∃ H' : Fin n → Fin n → ℕ, (∀ u v, H' u v = H' v u) ∧ (∀ v, H' v v = 0) ∧
      (∀ u v, H' u v ≠ 0 → u ∈ T ∧ v ∈ T) ∧
      (∀ v ∈ T, ∑ u, H' v u = 2 * N) ∧
      (∀ S : Finset (Fin n), (S ∩ T).Nonempty → (Sᶜ ∩ T).Nonempty →
        2 * N ≤ ∑ u ∈ S, ∑ v ∈ Sᶜ, H' u v) ∧
      ∑ u, ∑ v, (H' u v : ℝ) * c u v ≤ ∑ u, ∑ v, (H u v : ℝ) * c u v :=
  MetricTSP.eliminate_steiner2_thm c hc T hT2 N H hsym hdiag hdeg hcut
