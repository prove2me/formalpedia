-- Prove2me | solution 1 for MinimizingResolutionStrict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:00:06.537196+00:00
-- url     : https://prove2.me/submissions/6985ed66-ff4e-4285-ac24-fd4fc9d5eecb

import Definitions.Def_Tablet_smallPieceCount
import Definitions.Def_Tablet_MinimizingResolutionStrict

set_option autoImplicit false
open Set
theorem _root_.solution {E : Type*} [MetricSpace E] (γ : Curve E) (δ : ℝ) (hδ : 0 < δ)
    (k : ℕ) (s : ℕ → ℝ) (hres : IsGeodesicResolution γ k s)
    (hmin : ((Finset.Icc 1 k).filter (fun j => s j - s (j - 1) < δ)).card
      = smallPieceCount γ δ) :
    StrictMonoOn s (Set.Icc 0 k) := by
-- BODY
  obtain ⟨hmono, hs0, hsk, hedge⟩ := hres
  intro a ha b hb hab
  by_contra hcon
  push_neg at hcon
  have hak : a ≤ k := ha.2
  have hbk : b ≤ k := hb.2
  have hab' : s a ≤ s b := hmono ha hb hab.le
  have heq : s a = s b := le_antisymm hab' hcon
  have haj0 : (a + 1) ∈ Set.Icc (0 : ℕ) k := ⟨Nat.zero_le _, by omega⟩
  have h1 : s a ≤ s (a + 1) := hmono ha haj0 (by omega)
  have h2 : s (a + 1) ≤ s b := hmono haj0 hb (by omega)
  have hdeg : s a = s (a + 1) := le_antisymm h1 (h2.trans heq.symm.le)
  obtain ⟨j0, hj0eq⟩ : ∃ j0, j0 = a + 1 := ⟨a + 1, rfl⟩
  have hj0_1 : 1 ≤ j0 := by omega
  have hj0_k : j0 ≤ k := by omega
  have hdeg' : s (j0 - 1) = s j0 := by
    have hj0m1 : j0 - 1 = a := by omega
    rw [hj0m1, hj0eq]; exact hdeg
  -- the resolution with the degenerate breakpoint j0 dropped
  set s' : ℕ → ℝ := fun i => if i < j0 then s i else s (i + 1) with hs'def
  have hs'lt : ∀ i, i < j0 → s' i = s i := fun i hi => by simp [hs'def, hi]
  have hs'ge : ∀ i, j0 ≤ i → s' i = s (i + 1) := fun i hi => by
    simp [hs'def, not_lt.mpr hi]
  have hmono' : MonotoneOn s' (Set.Icc (0 : ℕ) (k - 1)) := by
    rintro a' ⟨-, ha'1⟩ b' ⟨-, hb'1⟩ hab'
    rcases lt_or_ge a' j0 with haj | haj
    · rcases lt_or_ge b' j0 with hbj | hbj
      · rw [hs'lt a' haj, hs'lt b' hbj]
        exact hmono ⟨Nat.zero_le _, by omega⟩ ⟨Nat.zero_le _, by omega⟩ hab'
      · rw [hs'lt a' haj, hs'ge b' hbj]
        have e1 : s a' ≤ s (j0 - 1) :=
          hmono ⟨Nat.zero_le _, by omega⟩ ⟨Nat.zero_le _, by omega⟩ (by omega)
        have e2 : s (j0 - 1) ≤ s (b' + 1) := by
          rw [hdeg']
          exact hmono ⟨Nat.zero_le _, by omega⟩ ⟨Nat.zero_le _, by omega⟩ (by omega)
        exact e1.trans e2
    · have hbj : j0 ≤ b' := le_trans haj hab'
      rw [hs'ge a' haj, hs'ge b' hbj]
      exact hmono ⟨Nat.zero_le _, by omega⟩ ⟨Nat.zero_le _, by omega⟩ (by omega)
  have hs'0 : s' 0 = 0 := by rw [hs'lt 0 (by omega)]; exact hs0
  have hs'end : s' (k - 1) = γ.len := by
    rcases hj0_k.lt_or_eq with hjk | hjk
    · rw [hs'ge (k - 1) (by omega), show k - 1 + 1 = k by omega]
      exact hsk
    · rw [hs'lt (k - 1) (by omega), show k - 1 = j0 - 1 by omega, hdeg', hjk]
      exact hsk
  have hedge' : ∀ i < k - 1, IsGeodesicOn γ (s' i) (s' (i + 1)) := by
    intro i hi
    rcases lt_or_ge (i + 1) j0 with hlt1 | hge1
    · have hi0 : i < j0 := by omega
      rw [hs'lt i hi0, hs'lt (i + 1) hlt1]
      exact hedge i (by omega)
    · rcases eq_or_lt_of_le hge1 with heq1 | hlt1
      · have hi0 : i < j0 := by omega
        rw [hs'lt i hi0, hs'ge (i + 1) hge1]
        have hi_eq : s i = s j0 := by
          have hij0 : i = j0 - 1 := by omega
          rw [hij0]; exact hdeg'
        have hidx : i + 1 + 1 = j0 + 1 := by omega
        rw [hi_eq, hidx]
        exact hedge j0 (by omega)
      · have hige : j0 ≤ i := by omega
        rw [hs'ge i hige, hs'ge (i + 1) hge1]
        exact hedge (i + 1) (by omega)
  have hgr' : IsGeodesicResolution γ (k - 1) s' := ⟨hmono', hs'0, hs'end, hedge'⟩
  -- j0 is a small edge of s
  have hj0mem : j0 ∈ (Finset.Icc 1 k).filter (fun j => s j - s (j - 1) < δ) := by
    have hz : s j0 - s (j0 - 1) = 0 := by rw [hdeg']; ring
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hj0_1, hj0_k⟩, by rw [hz]; exact hδ⟩
  set Small_s : Finset ℕ := (Finset.Icc 1 k).filter (fun j => s j - s (j - 1) < δ) with hSmall_s
  set Small_s' : Finset ℕ := (Finset.Icc 1 (k - 1)).filter (fun j => s' j - s' (j - 1) < δ)
    with hSmall_s'
  -- reindexing map φ : indices of s' ↦ indices of s (skipping j0), and its inverse ψ
  set φ : ℕ → ℕ := fun j => if j < j0 then j else j + 1 with hφdef
  set ψ : ℕ → ℕ := fun j => if j < j0 then j else j - 1 with hψdef
  have hφlt : ∀ j, j < j0 → φ j = j := fun j hj => by simp [hφdef, hj]
  have hφge : ∀ j, j0 ≤ j → φ j = j + 1 := fun j hj => by simp [hφdef, not_lt.mpr hj]
  have hψlt : ∀ j, j < j0 → ψ j = j := fun j hj => by simp [hψdef, hj]
  have hψge : ∀ j, j0 ≤ j → ψ j = j - 1 := fun j hj => by simp [hψdef, not_lt.mpr hj]
  -- the edge-length identity: s' j and s (φ j) bound the same edge
  have hedgelen : ∀ j, 1 ≤ j → j ≤ k - 1 → s' j - s' (j - 1) = s (φ j) - s (φ j - 1) := by
    intro j hj1 hjk1
    by_cases h1 : j < j0
    · have hjm1 : j - 1 < j0 := by omega
      rw [hφlt j h1, hs'lt j h1, hs'lt (j - 1) hjm1]
    · push_neg at h1
      rcases eq_or_lt_of_le h1 with heq | hlt
      · have hjm1lt : j - 1 < j0 := by omega
        rw [hφge j h1, hs'ge j h1, hs'lt (j - 1) hjm1lt]
        have hidx : j + 1 - 1 = j := by omega
        rw [hidx]
        have hswap : s (j - 1) = s j := by
          have hjeq : j - 1 = j0 - 1 := by omega
          rw [hjeq, hdeg', ← heq]
        rw [hswap]
      · have hjm1ge : j0 ≤ j - 1 := by omega
        rw [hφge j h1, hs'ge j h1, hs'ge (j - 1) hjm1ge]
        have hidx1 : j + 1 - 1 = j := by omega
        have hidx2 : j - 1 + 1 = j := by omega
        rw [hidx1, hidx2]
  have hmapsto1 : ∀ j, j ∈ Small_s' → φ j ∈ Small_s.erase j0 := by
    intro j hj
    obtain ⟨hjIcc, hjlt⟩ := Finset.mem_filter.mp hj
    obtain ⟨hj1, hjk1⟩ := Finset.mem_Icc.mp hjIcc
    have hedgeeq := hedgelen j hj1 hjk1
    rw [hedgeeq] at hjlt
    by_cases hcase : j < j0
    · rw [hφlt j hcase] at hjlt ⊢
      exact Finset.mem_erase.mpr ⟨by omega, Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨hj1, by omega⟩, hjlt⟩⟩
    · push_neg at hcase
      rw [hφge j hcase] at hjlt ⊢
      exact Finset.mem_erase.mpr ⟨by omega, Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, hjlt⟩⟩
  have hmapsto2 : ∀ j, j ∈ Small_s.erase j0 → ψ j ∈ Small_s' := by
    intro j hj
    obtain ⟨hjne, hjmem⟩ := Finset.mem_erase.mp hj
    obtain ⟨hjIcc, hjlt⟩ := Finset.mem_filter.mp hjmem
    obtain ⟨hj1, hjk⟩ := Finset.mem_Icc.mp hjIcc
    by_cases hcase : j < j0
    · rw [hψlt j hcase]
      have hjk1 : j ≤ k - 1 := by omega
      have hedgeeq := hedgelen j hj1 hjk1
      rw [hφlt j hcase] at hedgeeq
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hj1, hjk1⟩, by rw [hedgeeq]; exact hjlt⟩
    · push_neg at hcase
      have hcase' : j0 < j := lt_of_le_of_ne hcase (Ne.symm hjne)
      rw [hψge j hcase]
      have hjge1 : 1 ≤ j - 1 := by omega
      have hjle : j - 1 ≤ k - 1 := by omega
      have hedgeeq := hedgelen (j - 1) hjge1 hjle
      have hφeq : φ (j - 1) = j := by
        rw [hφge (j - 1) (by omega)]; omega
      rw [hφeq] at hedgeeq
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hjge1, hjle⟩, by rw [hedgeeq]; exact hjlt⟩
  have hleft : ∀ j, j ∈ Small_s' → ψ (φ j) = j := by
    intro j hj
    obtain ⟨hjIcc, -⟩ := Finset.mem_filter.mp hj
    obtain ⟨hj1, hjk1⟩ := Finset.mem_Icc.mp hjIcc
    by_cases hcase : j < j0
    · rw [hφlt j hcase, hψlt j hcase]
    · push_neg at hcase
      rw [hφge j hcase, hψge (j + 1) (by omega)]
      omega
  have hright : ∀ j, j ∈ Small_s.erase j0 → φ (ψ j) = j := by
    intro j hj
    obtain ⟨hjne, hjmem⟩ := Finset.mem_erase.mp hj
    obtain ⟨hjIcc, -⟩ := Finset.mem_filter.mp hjmem
    obtain ⟨hj1, hjk⟩ := Finset.mem_Icc.mp hjIcc
    by_cases hcase : j < j0
    · rw [hψlt j hcase, hφlt j hcase]
    · push_neg at hcase
      have hcase' : j0 < j := lt_of_le_of_ne hcase (Ne.symm hjne)
      rw [hψge j hcase, hφge (j - 1) (by omega)]
      omega
  have hcardeq : Small_s'.card = (Small_s.erase j0).card :=
    Finset.card_nbij' φ ψ hmapsto1 hmapsto2 hleft hright
  have herase : (Small_s.erase j0).card + 1 = Small_s.card :=
    Finset.card_erase_add_one hj0mem
  have hle : smallPieceCount γ δ ≤ Small_s'.card := by
    apply Nat.sInf_le
    exact ⟨k - 1, s', hgr', rfl⟩
  omega
