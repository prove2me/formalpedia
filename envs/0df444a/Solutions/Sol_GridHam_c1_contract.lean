-- Prove2me | solution 1 for GridHam.c1_contract
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:47:27.588799+00:00
-- url     : https://prove2.me/submissions/2b0e54fd-8f0d-418e-bde0-d6c0f6fbdf79

module
public import Definitions.Def_GridHam_StripSplit
public import Definitions.Def_GridHam_F3
public import Theorems.Thm_GridHam_pnext_mem_left
public import Theorems.Thm_GridHam_pnext_mem_right
public import Theorems.Thm_GridHam_pnext_adj
public import Theorems.Thm_GridHam_interior_two
public import Theorems.Thm_GridHam_pnext_reverse
public import Theorems.Thm_GridHam_contract_mid
public import Theorems.Thm_GridHam_c1_run
public import Theorems.Thm_GridHam_hasHamPath_reverse
public import Theorems.Thm_GridHam_mem_allCoords
public import Theorems.Thm_GridHam_validPath_reverse


set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution (w : ℕ) (u v : Coord) (hu : 2 ≤ u.1) (hv : 2 ≤ v.1)
    (h : HasHamPath w 3 u v) : HasHamPath (w - 2) 3 (shiftL2 u) (shiftL2 v) := by
  have hM1 : ∀ c : Coord, c.1 < 2 → c.2 < 3 →
      c ∈ [(1, 1), (1, 0), (0, 0), (0, 1), (0, 2), (1, 2)] := by
    intro c h1 h2
    obtain ⟨c1, c2⟩ := c
    dsimp only at h1 h2
    simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false]
    omega
  have hMx1 : ∀ c ∈ [(1, 1), (1, 0), (0, 0), (0, 1), (0, 2), (1, 2)], c.1 < 2 := by
    intro c hc
    obtain ⟨c1, c2⟩ := c
    simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hc
    show c1 < 2
    omega
  have hM2 : ∀ c : Coord, c.1 < 2 → c.2 < 3 →
      c ∈ [(1, 0), (0, 0), (0, 1), (0, 2), (1, 2), (1, 1)] := by
    intro c h1 h2
    obtain ⟨c1, c2⟩ := c
    dsimp only at h1 h2
    simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false]
    omega
  have hMx2 : ∀ c ∈ [(1, 0), (0, 0), (0, 1), (0, 2), (1, 2), (1, 1)], c.1 < 2 := by
    intro c hc
    obtain ⟨c1, c2⟩ := c
    simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hc
    show c1 < 2
    omega
  have core : ∀ (u v : Coord) (p : List Coord), 2 ≤ u.1 → 2 ≤ v.1 →
      ValidPath w 3 u v p → PNext p (0, 0) (0, 1) →
      HasHamPath (w - 2) 3 (shiftL2 u) (shiftL2 v) := by
    intro u v p hu hv hvp t1
    rcases c1_run w u v p hu hv hvp t1 with ⟨L, R, e⟩ | ⟨L, R, e⟩
    · rw [e] at hvp
      exact ⟨_, contract_mid w u v (2, 1) (2, 2) L [(1, 1), (1, 0), (0, 0), (0, 1), (0, 2), (1, 2)] R
        hM1 hMx1 rfl (by unfold Adjacent; dsimp only; omega) hvp⟩
    · rw [e] at hvp
      exact ⟨_, contract_mid w u v (2, 0) (2, 1) L [(1, 0), (0, 0), (0, 1), (0, 2), (1, 2), (1, 1)] R
        hM2 hMx2 rfl (by unfold Adjacent; dsimp only; omega) hvp⟩
  obtain ⟨p, hvp⟩ := h
  by_cases hor : PNext p (0, 0) (0, 1)
  · exact core u v p hu hv hvp hor
  · -- then (0,1) comes right before (0,0); reverse the path
    have hBA : PNext p (0, 1) (0, 0) := by
      have hvp' := hvp
      obtain ⟨hlen, hhead, hlast, hnd, hin, hcov, hch⟩ := hvp'
      have hum : u ∈ p := by
        cases p with
        | nil => simp at hhead
        | cons a l =>
          have hau : a = u := by simpa using hhead
          rw [hau]
          simp
      have huin := hin u hum
      unfold InBounds at huin
      have m00 := hcov (0, 0) ((mem_allCoords w 3 _).mpr ⟨by show 0 < w; omega, by show 0 < 3; omega⟩)
      have hnh : p.head? ≠ some (0, 0) := by
        intro e
        rw [hhead] at e
        have := congrArg Prod.fst (Option.some.inj e)
        dsimp only at this
        omega
      have hnl : p.getLast? ≠ some (0, 0) := by
        intro e
        rw [hlast] at e
        have := congrArg Prod.fst (Option.some.inj e)
        dsimp only at this
        omega
      obtain ⟨a, b, hab, hpa, hpb⟩ := interior_two hnd m00 hnh hnl
      have hcand : ∀ y ∈ p, (Adjacent y (0, 0) ∨ Adjacent (0, 0) y) → y = (0, 1) ∨ y = (1, 0) := by
        intro y hy hadj
        have hyb := hin y hy
        unfold InBounds at hyb
        obtain ⟨y1, y2⟩ := y
        unfold Adjacent at hadj
        dsimp only at hadj hyb
        simp only [Prod.mk.injEq]
        omega
      have ha := hcand a (pnext_mem_left hpa) (Or.inl (pnext_adj hch hpa))
      have hb := hcand b (pnext_mem_right hpb) (Or.inr (pnext_adj hch hpb))
      rcases hb with hb | hb
      · rw [hb] at hpb
        exact absurd hpb hor
      · rcases ha with ha | ha
        · rw [ha] at hpa
          exact hpa
        · exact absurd (ha.trans hb.symm) hab
    have hvr := validPath_reverse hvp
    exact hasHamPath_reverse (core v u p.reverse hv hu hvr (pnext_reverse hBA))
end GridHam
