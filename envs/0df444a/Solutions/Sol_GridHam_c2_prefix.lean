-- Prove2me | solution 1 for GridHam.c2_prefix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:38:01.745728+00:00
-- url     : https://prove2.me/submissions/8200ec2f-ff76-4e00-be07-35e37ddf1d18

module
public import Definitions.Def_GridHam_StripSplit
public import Definitions.Def_GridHam_F3
public import Theorems.Thm_GridHam_pnext_mem_left
public import Theorems.Thm_GridHam_pnext_mem_right
public import Theorems.Thm_GridHam_pnext_adj
public import Theorems.Thm_GridHam_pnext_unique_right
public import Theorems.Thm_GridHam_pnext_unique_left
public import Theorems.Thm_GridHam_no_prev_of_head
public import Theorems.Thm_GridHam_interior_two
public import Theorems.Thm_GridHam_forced_after_head
public import Theorems.Thm_GridHam_pnext_pos
public import Theorems.Thm_GridHam_next_forced
public import Theorems.Thm_GridHam_mem_allCoords
public import Theorems.Thm_P2M_GridHam_mem_of_getLast__beac85f634f6


set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution (w : ℕ) (v : Coord) (p : List Coord) (hv2 : 2 ≤ v.1)
    (hvp : ValidPath w 3 (1, 0) v p) :
    ∃ R, p = (1, 0) :: (0, 0) :: (0, 1) :: (0, 2) :: (1, 2) :: (1, 1) :: (2, 1) :: R := by
  obtain ⟨hlen, hhead, hlast, hnd, hin, hcov, hch⟩ := hvp
  have hvin := hin v (mem_of_getLast? p v hlast)
  unfold InBounds at hvin
  have hmem : ∀ c : Coord, c.1 < w → c.2 < 3 → c ∈ p :=
    fun c h1 h2 => hcov c ((mem_allCoords w 3 c).mpr ⟨h1, h2⟩)
  have hnothead : ∀ c : Coord, c ≠ (1, 0) → p.head? ≠ some c := by
    intro c hc e
    rw [hhead] at e
    exact hc (Option.some.inj e).symm
  have hnotlast : ∀ c : Coord, c.1 < 2 → p.getLast? ≠ some c := by
    intro c hc e
    rw [hlast] at e
    have := congrArg Prod.fst (Option.some.inj e)
    omega
  have hbd : ∀ y ∈ p, y.1 < w ∧ y.2 < 3 := fun y hy => hin y hy
  have m00 := hmem (0, 0) (by show 0 < w; omega) (by show 0 < 3; omega)
  have m02 := hmem (0, 2) (by show 0 < w; omega) (by show 2 < 3; omega)
  have m11 := hmem (1, 1) (by show 1 < w; omega) (by show 1 < 3; omega)
  -- (0,0) comes right after the start, then (0,1)
  have s1 : PNext p (1, 0) (0, 0) := by
    apply forced_after_head (z := (0, 1)) hnd hch hhead m00 (hnothead (0, 0) (by simp))
      (hnotlast (0, 0) (by show 0 < 2; omega))
    intro y hy hadj
    have hyb := hbd y hy
    obtain ⟨y1, y2⟩ := y
    unfold Adjacent at hadj
    dsimp only at hadj hyb
    simp only [Prod.mk.injEq]
    omega
  have s2 : PNext p (0, 0) (0, 1) := by
    apply next_forced hnd hch m00 (hnothead (0, 0) (by simp))
      (hnotlast (0, 0) (by show 0 < 2; omega)) s1
    intro y hy hadj
    have hyb := hbd y hy
    obtain ⟨y1, y2⟩ := y
    unfold Adjacent at hadj
    dsimp only at hadj hyb
    simp only [Prod.mk.injEq]
    omega
  -- (0,2) sits between (0,1) and (1,2)
  obtain ⟨s3, s4⟩ : PNext p (0, 1) (0, 2) ∧ PNext p (0, 2) (1, 2) := by
    obtain ⟨a, b, hab, hpa, hpb⟩ :=
      interior_two hnd m02 (hnothead (0, 2) (by simp)) (hnotlast (0, 2) (by show 0 < 2; omega))
    have ha : a = (0, 1) ∨ a = (1, 2) := by
      have hadj := pnext_adj hch hpa
      have hyb := hbd a (pnext_mem_left hpa)
      clear hpa hpb hab
      obtain ⟨a1, a2⟩ := a
      unfold Adjacent at hadj
      dsimp only at hadj hyb
      simp only [Prod.mk.injEq]
      omega
    have hb : b = (0, 1) ∨ b = (1, 2) := by
      have hadj := pnext_adj hch hpb
      have hyb := hbd b (pnext_mem_right hpb)
      clear hpa hpb hab
      obtain ⟨b1, b2⟩ := b
      unfold Adjacent at hadj
      dsimp only at hadj hyb
      simp only [Prod.mk.injEq]
      omega
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact absurd (ha.trans hb.symm) hab
    · rw [ha] at hpa
      rw [hb] at hpb
      exact ⟨hpa, hpb⟩
    · exfalso
      rw [hb] at hpb
      have := pnext_unique_left hnd hpb s2
      simp at this
    · exact absurd (ha.trans hb.symm) hab
  -- (1,1) sits between (1,2) and (2,1)
  obtain ⟨s5, s6⟩ : PNext p (1, 2) (1, 1) ∧ PNext p (1, 1) (2, 1) := by
    obtain ⟨a, b, hab, hpa, hpb⟩ :=
      interior_two hnd m11 (hnothead (1, 1) (by simp)) (hnotlast (1, 1) (by show 1 < 2; omega))
    have ha : a = (1, 2) ∨ a = (2, 1) := by
      have hcand : a = (0, 1) ∨ a = (1, 0) ∨ a = (1, 2) ∨ a = (2, 1) := by
        have hadj := pnext_adj hch hpa
        have hyb := hbd a (pnext_mem_left hpa)
        clear hpa hpb hab
        obtain ⟨a1, a2⟩ := a
        unfold Adjacent at hadj
        dsimp only at hadj hyb
        simp only [Prod.mk.injEq]
        omega
      rcases hcand with h | h | h | h
      · exfalso
        rw [h] at hpa
        have := pnext_unique_right hnd hpa s3
        simp at this
      · exfalso
        rw [h] at hpa
        have := pnext_unique_right hnd hpa s1
        simp at this
      · exact Or.inl h
      · exact Or.inr h
    have hb : b = (1, 2) ∨ b = (2, 1) := by
      have hcand : b = (0, 1) ∨ b = (1, 0) ∨ b = (1, 2) ∨ b = (2, 1) := by
        have hadj := pnext_adj hch hpb
        have hyb := hbd b (pnext_mem_right hpb)
        clear hpa hpb hab
        obtain ⟨b1, b2⟩ := b
        unfold Adjacent at hadj
        dsimp only at hadj hyb
        simp only [Prod.mk.injEq]
        omega
      rcases hcand with h | h | h | h
      · exfalso
        rw [h] at hpb
        have := pnext_unique_left hnd hpb s2
        simp at this
      · exfalso
        rw [h] at hpb
        exact no_prev_of_head hnd hhead hpb
      · exact Or.inl h
      · exact Or.inr h
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact absurd (ha.trans hb.symm) hab
    · rw [ha] at hpa
      rw [hb] at hpb
      exact ⟨hpa, hpb⟩
    · exfalso
      rw [hb] at hpb
      have := pnext_unique_left hnd hpb s4
      simp at this
    · exact absurd (ha.trans hb.symm) hab
  -- read the forced opening off the list
  cases p with
  | nil => simp at hhead
  | cons c0 r0 =>
    have hc0 : c0 = (1, 0) := by simpa using hhead
    subst hc0
    obtain ⟨r1, h1⟩ := pnext_pos (L := []) hnd rfl s1
    subst h1
    obtain ⟨r2, h2⟩ := pnext_pos (L := [(1, 0)]) hnd rfl s2
    subst h2
    obtain ⟨r3, h3⟩ := pnext_pos (L := [(1, 0), (0, 0)]) hnd rfl s3
    subst h3
    obtain ⟨r4, h4⟩ := pnext_pos (L := [(1, 0), (0, 0), (0, 1)]) hnd rfl s4
    subst h4
    obtain ⟨r5, h5⟩ := pnext_pos (L := [(1, 0), (0, 0), (0, 1), (0, 2)]) hnd rfl s5
    subst h5
    obtain ⟨r6, h6⟩ := pnext_pos (L := [(1, 0), (0, 0), (0, 1), (0, 2), (1, 2)]) hnd rfl s6
    subst h6
    exact ⟨r6, rfl⟩
end GridHam
