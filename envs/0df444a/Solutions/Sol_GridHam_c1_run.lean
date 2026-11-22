-- Prove2me | solution 1 for GridHam.c1_run
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:42:06.944247+00:00
-- url     : https://prove2.me/submissions/132f787a-d2c1-4ef1-8476-99a1389606a6

module
public import Definitions.Def_GridHam_StripSplit
public import Definitions.Def_GridHam_F3
public import Theorems.Thm_GridHam_pnext_mem_left
public import Theorems.Thm_GridHam_pnext_mem_right
public import Theorems.Thm_GridHam_pnext_adj
public import Theorems.Thm_GridHam_split_unique
public import Theorems.Thm_GridHam_pnext_unique_right
public import Theorems.Thm_GridHam_pnext_unique_left
public import Theorems.Thm_GridHam_interior_two
public import Theorems.Thm_GridHam_pnext_step
public import Theorems.Thm_GridHam_mem_allCoords


set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution (w : ℕ) (u v : Coord) (p : List Coord) (hu : 2 ≤ u.1) (hv2 : 2 ≤ v.1)
    (hvp : ValidPath w 3 u v p) (t1 : PNext p (0, 0) (0, 1)) :
    (∃ L R, p = L ++ (2, 1) :: (1, 1) :: (1, 0) :: (0, 0) :: (0, 1) :: (0, 2) :: (1, 2) :: (2, 2) :: R) ∨
    (∃ L R, p = L ++ (2, 0) :: (1, 0) :: (0, 0) :: (0, 1) :: (0, 2) :: (1, 2) :: (1, 1) :: (2, 1) :: R) := by
  obtain ⟨hlen, hhead, hlast, hnd, hin, hcov, hch⟩ := hvp
  have hum : u ∈ p := by
    cases p with
    | nil => simp at hhead
    | cons a l =>
      have hau : a = u := by simpa using hhead
      rw [hau]
      simp
  have huin := hin u hum
  unfold InBounds at huin
  have hmem : ∀ c : Coord, c.1 < w → c.2 < 3 → c ∈ p :=
    fun c h1 h2 => hcov c ((mem_allCoords w 3 c).mpr ⟨h1, h2⟩)
  have hnh : ∀ c : Coord, c.1 < 2 → p.head? ≠ some c := by
    intro c hc e
    rw [hhead] at e
    have := congrArg Prod.fst (Option.some.inj e)
    omega
  have hnl : ∀ c : Coord, c.1 < 2 → p.getLast? ≠ some c := by
    intro c hc e
    rw [hlast] at e
    have := congrArg Prod.fst (Option.some.inj e)
    omega
  have hbd : ∀ y ∈ p, y.1 < w ∧ y.2 < 3 := fun y hy => hin y hy
  have m00 := hmem (0, 0) (by show 0 < w; omega) (by show 0 < 3; omega)
  have m02 := hmem (0, 2) (by show 0 < w; omega) (by show 2 < 3; omega)
  have m10 := hmem (1, 0) (by show 1 < w; omega) (by show 0 < 3; omega)
  have m11 := hmem (1, 1) (by show 1 < w; omega) (by show 1 < 3; omega)
  have m12 := hmem (1, 2) (by show 1 < w; omega) (by show 2 < 3; omega)
  -- (1,0) → (0,0)
  have t0 : PNext p (1, 0) (0, 0) := by
    obtain ⟨a, b, hab, hpa, hpb⟩ :=
      interior_two hnd m00 (hnh (0, 0) (by show 0 < 2; omega)) (hnl (0, 0) (by show 0 < 2; omega))
    have hb := pnext_unique_right hnd hpb t1
    have ha : a = (0, 1) ∨ a = (1, 0) := by
      have hadj := pnext_adj hch hpa
      have hyb := hbd a (pnext_mem_left hpa)
      clear hpa hpb hab hb
      obtain ⟨a1, a2⟩ := a
      unfold Adjacent at hadj
      dsimp only at hadj hyb
      simp only [Prod.mk.injEq]
      omega
    rcases ha with ha | ha
    · exact absurd (ha.trans hb.symm) hab
    · rw [ha] at hpa
      exact hpa
  -- (0,1) → (0,2) → (1,2)
  obtain ⟨t2, t3⟩ : PNext p (0, 1) (0, 2) ∧ PNext p (0, 2) (1, 2) := by
    obtain ⟨a, b, hab, hpa, hpb⟩ :=
      interior_two hnd m02 (hnh (0, 2) (by show 0 < 2; omega)) (hnl (0, 2) (by show 0 < 2; omega))
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
      have := pnext_unique_left hnd hpb t1
      simp at this
    · exact absurd (ha.trans hb.symm) hab
  -- (1,1): predecessor in {(1,2),(2,1)}, successor in {(1,0),(2,1)}
  obtain ⟨e0, e1, hne, hpe0, hpe1⟩ :=
    interior_two hnd m11 (hnh (1, 1) (by show 1 < 2; omega)) (hnl (1, 1) (by show 1 < 2; omega))
  have he0 : e0 = (1, 2) ∨ e0 = (2, 1) := by
    have hcand : e0 = (0, 1) ∨ e0 = (1, 0) ∨ e0 = (1, 2) ∨ e0 = (2, 1) := by
      have hadj := pnext_adj hch hpe0
      have hyb := hbd e0 (pnext_mem_left hpe0)
      clear hpe0 hpe1 hne
      obtain ⟨a1, a2⟩ := e0
      unfold Adjacent at hadj
      dsimp only at hadj hyb
      simp only [Prod.mk.injEq]
      omega
    rcases hcand with h | h | h | h
    · exfalso
      rw [h] at hpe0
      have := pnext_unique_right hnd hpe0 t2
      simp at this
    · exfalso
      rw [h] at hpe0
      have := pnext_unique_right hnd hpe0 t0
      simp at this
    · exact Or.inl h
    · exact Or.inr h
  have he1 : e1 = (1, 0) ∨ e1 = (2, 1) := by
    have hcand : e1 = (0, 1) ∨ e1 = (1, 0) ∨ e1 = (1, 2) ∨ e1 = (2, 1) := by
      have hadj := pnext_adj hch hpe1
      have hyb := hbd e1 (pnext_mem_right hpe1)
      clear hpe0 hpe1 hne
      obtain ⟨a1, a2⟩ := e1
      unfold Adjacent at hadj
      dsimp only at hadj hyb
      simp only [Prod.mk.injEq]
      omega
    rcases hcand with h | h | h | h
    · exfalso
      rw [h] at hpe1
      have := pnext_unique_left hnd hpe1 t1
      simp at this
    · exact Or.inl h
    · exfalso
      rw [h] at hpe1
      have := pnext_unique_left hnd hpe1 t3
      simp at this
    · exact Or.inr h
  rcases he0 with he0 | he0 <;> rcases he1 with he1 | he1
  · -- (1,2) → (1,1) → (1,0): a cycle through all six cells, impossible
    exfalso
    rw [he0] at hpe0
    rw [he1] at hpe1
    obtain ⟨L, R, hp⟩ := List.append_of_mem m10
    obtain ⟨R1, q1⟩ := pnext_step hnd hp t0
    obtain ⟨R2, q2⟩ := pnext_step hnd q1 t1
    obtain ⟨R3, q3⟩ := pnext_step hnd q2 t2
    obtain ⟨R4, q4⟩ := pnext_step hnd q3 t3
    obtain ⟨R5, q5⟩ := pnext_step hnd q4 hpe0
    obtain ⟨R6, q6⟩ := pnext_step hnd q5 hpe1
    have hnd' : (L ++ (1, 0) :: R).Nodup := by rw [← hp]; exact hnd
    have hsu := split_unique L _ R R6 (1, 0) hnd' (hp.symm.trans q6)
    have hl := congrArg List.length hsu.1
    simp at hl
  · -- (1,2) → (1,1) → (2,1): the run starts (2,0) → (1,0)
    rw [he0] at hpe0
    rw [he1] at hpe1
    have t4 : PNext p (2, 0) (1, 0) := by
      obtain ⟨a, b, hab, hpa, hpb⟩ :=
        interior_two hnd m10 (hnh (1, 0) (by show 1 < 2; omega)) (hnl (1, 0) (by show 1 < 2; omega))
      have hb := pnext_unique_right hnd hpb t0
      have hcand : a = (0, 0) ∨ a = (1, 1) ∨ a = (2, 0) := by
        have hadj := pnext_adj hch hpa
        have hyb := hbd a (pnext_mem_left hpa)
        clear hpa hpb hab hb
        obtain ⟨a1, a2⟩ := a
        unfold Adjacent at hadj
        dsimp only at hadj hyb
        simp only [Prod.mk.injEq]
        omega
      rcases hcand with h | h | h
      · exact absurd (h.trans hb.symm) hab
      · exfalso
        rw [h] at hpa
        have := pnext_unique_right hnd hpa hpe1
        simp at this
      · rw [h] at hpa
        exact hpa
    have m20 := hmem (2, 0) (by show 2 < w; omega) (by show 0 < 3; omega)
    obtain ⟨L, R, hp⟩ := List.append_of_mem m20
    obtain ⟨R1, q1⟩ := pnext_step hnd hp t4
    obtain ⟨R2, q2⟩ := pnext_step hnd q1 t0
    obtain ⟨R3, q3⟩ := pnext_step hnd q2 t1
    obtain ⟨R4, q4⟩ := pnext_step hnd q3 t2
    obtain ⟨R5, q5⟩ := pnext_step hnd q4 t3
    obtain ⟨R6, q6⟩ := pnext_step hnd q5 hpe0
    obtain ⟨R7, q7⟩ := pnext_step hnd q6 hpe1
    exact Or.inr ⟨L, R7, by rw [q7]; simp⟩
  · -- (2,1) → (1,1) → (1,0): the run ends (1,2) → (2,2)
    rw [he0] at hpe0
    rw [he1] at hpe1
    have t5 : PNext p (1, 2) (2, 2) := by
      obtain ⟨a, b, hab, hpa, hpb⟩ :=
        interior_two hnd m12 (hnh (1, 2) (by show 1 < 2; omega)) (hnl (1, 2) (by show 1 < 2; omega))
      have ha := pnext_unique_left hnd hpa t3
      have hcand : b = (0, 2) ∨ b = (1, 1) ∨ b = (2, 2) := by
        have hadj := pnext_adj hch hpb
        have hyb := hbd b (pnext_mem_right hpb)
        clear hpa hpb hab ha
        obtain ⟨b1, b2⟩ := b
        unfold Adjacent at hadj
        dsimp only at hadj hyb
        simp only [Prod.mk.injEq]
        omega
      rcases hcand with h | h | h
      · exact absurd (ha.trans h.symm) hab
      · exfalso
        rw [h] at hpb
        have := pnext_unique_left hnd hpb hpe0
        simp at this
      · rw [h] at hpb
        exact hpb
    have m21 := hmem (2, 1) (by show 2 < w; omega) (by show 1 < 3; omega)
    obtain ⟨L, R, hp⟩ := List.append_of_mem m21
    obtain ⟨R1, q1⟩ := pnext_step hnd hp hpe0
    obtain ⟨R2, q2⟩ := pnext_step hnd q1 hpe1
    obtain ⟨R3, q3⟩ := pnext_step hnd q2 t0
    obtain ⟨R4, q4⟩ := pnext_step hnd q3 t1
    obtain ⟨R5, q5⟩ := pnext_step hnd q4 t2
    obtain ⟨R6, q6⟩ := pnext_step hnd q5 t3
    obtain ⟨R7, q7⟩ := pnext_step hnd q6 t5
    exact Or.inl ⟨L, R7, by rw [q7]; simp⟩
  · exact absurd (he0.trans he1.symm) hne
end GridHam
