-- Prove2me | solution 1 for GridHam.forbiddenCase1_implies_no_path
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:26:17.081476+00:00
-- url     : https://prove2.me/submissions/b10802df-c52a-4972-9daf-26a0b100496b

module
public import Definitions.Def_GridHam_Coloring
public import Definitions.Def_GridHam_Forbidden
public import Theorems.Thm_GridHam_unitChain_endpoints
public import Theorems.Thm_GridHam_nodup_map_of_injOn
public import Theorems.Thm_GridHam_unitStepChain_map
public import Theorems.Thm_P2M_GridHam_getLast__map_of_0a3c51641c72
public import Theorems.Thm_GridHam_forbiddenCase1_w1
public import Theorems.Thm_GridHam_forbiddenCase1_h1

set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution (width height : ℕ) (s t : Coord)
    (hs : InBounds width height s) (ht : InBounds width height t)
    (h1 : width = 1 ∨ height = 1) (hf : ForbiddenCase1 width height s t) :
    ¬ HasHamPath width height s t := by
  rintro ⟨p, hlen, hhead, hlast, hnd, hin, hcov, hch⟩
  cases p with
  | nil => simp at hhead
  | cons a prest =>
    have has : a = s := by simpa using hhead
    unfold InBounds at hs ht
    by_cases hw : width = 1
    · -- Width 1: every x-coordinate is 0; project to y.
      have hfst : ∀ v ∈ a :: prest, v.1 = 0 := by
        intro v hv
        have hv' := hin v hv
        unfold InBounds at hv'
        omega
      have hnd' : ((a :: prest).map Prod.snd).Nodup :=
        nodup_map_of_injOn Prod.snd (a :: prest) (fun v hv w hw' he => by
          have e1 := hfst v hv
          have e2 := hfst w hw'
          ext <;> omega) hnd
      have hch' : unitStepChain ((a :: prest).map Prod.snd) = true :=
        unitStepChain_map Prod.snd (a :: prest) (fun v hv w hw' hadj => by
          have e1 := hfst v hv
          have e2 := hfst w hw'
          unfold Adjacent at hadj
          rcases hadj with ⟨_, h4⟩ | ⟨_, h4⟩
          · exact h4
          · exfalso
            rcases h4 with h4 | h4 <;> omega) hch
      have hlenp : prest.length + 1 = height := by
        have hl0 : (a :: prest).length = prest.length + 1 := rfl
        rw [hw] at hlen
        omega
      have hl : (prest.map Prod.snd).length = prest.length := by simp
      have hcovq : ∀ y, y ∈ a.2 :: prest.map Prod.snd ↔
          0 ≤ y ∧ y ≤ 0 + (prest.map Prod.snd).length := by
        intro y
        have e : a.2 :: prest.map Prod.snd = (a :: prest).map Prod.snd := rfl
        rw [e]
        constructor
        · intro hy
          obtain ⟨v, hv, hve⟩ := List.mem_map.mp hy
          have hv' := hin v hv
          unfold InBounds at hv'
          exact ⟨by omega, by omega⟩
        · intro hy
          have hmem : ((0, y) : Coord) ∈ allCoords width height := by
            simp only [allCoords, List.mem_flatMap, List.mem_range, List.mem_map]
            exact ⟨0, by omega, y, by omega, rfl⟩
          exact List.mem_map.mpr ⟨(0, y), hcov (0, y) hmem, rfl⟩
      have hlastq : (a.2 :: prest.map Prod.snd).getLast? = some t.2 :=
        getLast?_map_of Prod.snd (a :: prest) t hlast
      have hres := unitChain_endpoints a.2 (prest.map Prod.snd) 0 hnd' hch' hcovq
      rw [hw] at hf
      have hf' := (forbiddenCase1_w1 height s t).mp hf
      rw [has] at hres hlastq
      rcases hres with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · rw [hlastq] at e2
        have e3 := Option.some.inj e2
        apply hf'
        left
        constructor
        · ext
          · show s.1 = 0; omega
          · show s.2 = 0; omega
        · ext
          · show t.1 = 0; omega
          · show t.2 = height - 1; omega
      · rw [hlastq] at e2
        have e3 := Option.some.inj e2
        apply hf'
        right
        constructor
        · ext
          · show s.1 = 0; omega
          · show s.2 = height - 1; omega
        · ext
          · show t.1 = 0; omega
          · show t.2 = 0; omega
    · -- Height 1 (and width ≠ 1): every y-coordinate is 0; project to x.
      have hh : height = 1 := h1.resolve_left hw
      have hsnd : ∀ v ∈ a :: prest, v.2 = 0 := by
        intro v hv
        have hv' := hin v hv
        unfold InBounds at hv'
        omega
      have hnd' : ((a :: prest).map Prod.fst).Nodup :=
        nodup_map_of_injOn Prod.fst (a :: prest) (fun v hv w hw' he => by
          have e1 := hsnd v hv
          have e2 := hsnd w hw'
          ext <;> omega) hnd
      have hch' : unitStepChain ((a :: prest).map Prod.fst) = true :=
        unitStepChain_map Prod.fst (a :: prest) (fun v hv w hw' hadj => by
          have e1 := hsnd v hv
          have e2 := hsnd w hw'
          unfold Adjacent at hadj
          rcases hadj with ⟨_, h4⟩ | ⟨_, h4⟩
          · exfalso
            rcases h4 with h4 | h4 <;> omega
          · exact h4) hch
      have hlenp : prest.length + 1 = width := by
        have hl0 : (a :: prest).length = prest.length + 1 := rfl
        rw [hh] at hlen
        omega
      have hl : (prest.map Prod.fst).length = prest.length := by simp
      have hcovq : ∀ x, x ∈ a.1 :: prest.map Prod.fst ↔
          0 ≤ x ∧ x ≤ 0 + (prest.map Prod.fst).length := by
        intro x
        have e : a.1 :: prest.map Prod.fst = (a :: prest).map Prod.fst := rfl
        rw [e]
        constructor
        · intro hx
          obtain ⟨v, hv, hve⟩ := List.mem_map.mp hx
          have hv' := hin v hv
          unfold InBounds at hv'
          exact ⟨by omega, by omega⟩
        · intro hx
          have hmem : ((x, 0) : Coord) ∈ allCoords width height := by
            simp only [allCoords, List.mem_flatMap, List.mem_range, List.mem_map]
            exact ⟨x, by omega, 0, by omega, rfl⟩
          exact List.mem_map.mpr ⟨(x, 0), hcov (x, 0) hmem, rfl⟩
      have hlastq : (a.1 :: prest.map Prod.fst).getLast? = some t.1 :=
        getLast?_map_of Prod.fst (a :: prest) t hlast
      have hres := unitChain_endpoints a.1 (prest.map Prod.fst) 0 hnd' hch' hcovq
      rw [hh] at hf
      have hf' := (forbiddenCase1_h1 width s t hw).mp hf
      rw [has] at hres hlastq
      rcases hres with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · rw [hlastq] at e2
        have e3 := Option.some.inj e2
        apply hf'
        left
        constructor
        · ext
          · show s.1 = 0; omega
          · show s.2 = 0; omega
        · ext
          · show t.1 = width - 1; omega
          · show t.2 = 0; omega
      · rw [hlastq] at e2
        have e3 := Option.some.inj e2
        apply hf'
        right
        constructor
        · ext
          · show s.1 = width - 1; omega
          · show s.2 = 0; omega
        · ext
          · show t.1 = 0; omega
          · show t.2 = 0; omega
end GridHam
