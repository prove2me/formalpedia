-- Prove2me | solution 1 for GridHam.splitVertically_preserves_startLeft
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:27:08.842124+00:00
-- url     : https://prove2.me/submissions/305c3b85-99ae-4295-855a-22cf1a65bdd1

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_StripSplit
public import Theorems.Thm_GridHam_mem_allCoords
public import Theorems.Thm_GridHam_nodup_append_of
public import Theorems.Thm_GridHam_nodup_map_coord
public import Theorems.Thm_GridHam_chainAdjacent_map_shiftX
public import Theorems.Thm_GridHam_chainAdjacent_append
public import Theorems.Thm_P2M_GridHam_getLast__append_cons_527000d4767a
public import Theorems.Thm_P2M_GridHam_getLast__map_coord_39a438577d66

set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution
    (width height cut cutRow : ℕ) (s t : Coord)
    (_hstartLeft : s.1 < t.1)
    (_hcutRange : s.1 ≤ cut) (hcutRange' : cut < t.1)
    (_hcutRow : cutRow < height)
    (hleft : HasHamPath (cut + 1) height s (cut, cutRow))
    (hright : HasHamPath (width - (cut + 1)) height (0, cutRow)
      (t.1 - (cut + 1), t.2)) :
    HasHamPath width height s t := by
  obtain ⟨pL, lenL, headL, lastL, ndL, inL, covL, chL⟩ := hleft
  obtain ⟨pR, lenR, headR, lastR, ndR, inR, covR, chR⟩ := hright
  cases pR with
  | nil => simp at headR
  | cons b restR =>
    have hb : b = (0, cutRow) := by simpa using headR
    have hbin := inR b (List.mem_cons.mpr (Or.inl rfl))
    unfold InBounds at hbin
    have hwide : cut + 1 < width := by omega
    have hle : cut + 1 ≤ width := by omega
    unfold HasHamPath
    refine ⟨pL ++ (b :: restR).map (shiftX (cut + 1)), ?_⟩
    unfold ValidPath
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- length
      rw [List.length_append, List.length_map, lenL, lenR, ← Nat.add_mul,
        Nat.add_sub_of_le hle]
    · -- head
      cases pL with
      | nil => simp at headL
      | cons a restL => simpa using headL
    · -- last
      rw [show (b :: restR).map (shiftX (cut + 1)) =
          shiftX (cut + 1) b :: restR.map (shiftX (cut + 1)) from rfl,
        getLast?_append_cons,
        show shiftX (cut + 1) b :: restR.map (shiftX (cut + 1)) =
          (b :: restR).map (shiftX (cut + 1)) from rfl,
        getLast?_map_coord (shiftX (cut + 1)) (b :: restR) _ lastR]
      congr 1
      unfold shiftX
      ext
      · show t.1 - (cut + 1) + (cut + 1) = t.1
        omega
      · rfl
    · -- no repeats
      apply nodup_append_of pL _ ndL
      · apply nodup_map_coord (shiftX (cut + 1)) _ (b :: restR) ndR
        intro v w hvw
        unfold shiftX at hvw
        have h1 := congrArg Prod.fst hvw
        have h2 := congrArg Prod.snd hvw
        dsimp only at h1 h2
        ext
        · omega
        · omega
      · intro v hv w hw
        obtain ⟨u, _, rfl⟩ := List.mem_map.mp hw
        have hv' := inL v hv
        unfold InBounds at hv'
        intro heq
        have h1 := congrArg Prod.fst heq
        unfold shiftX at h1
        dsimp only at h1
        omega
    · -- every vertex in bounds
      intro v hv
      rcases List.mem_append.mp hv with h | h
      · have hv' := inL v h
        unfold InBounds at hv' ⊢
        exact ⟨by omega, hv'.2⟩
      · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp h
        have hu' := inR u hu
        unfold InBounds at hu' ⊢
        unfold shiftX
        dsimp only
        exact ⟨by omega, hu'.2⟩
    · -- every grid vertex covered
      intro v hv
      obtain ⟨hvx, hvy⟩ := (mem_allCoords width height v).mp hv
      by_cases hc : v.1 ≤ cut
      · exact List.mem_append.mpr (Or.inl
          (covL v ((mem_allCoords (cut + 1) height v).mpr ⟨by omega, hvy⟩)))
      · have hu := covR (v.1 - (cut + 1), v.2)
          ((mem_allCoords (width - (cut + 1)) height _).mpr ⟨by dsimp only; omega, hvy⟩)
        refine List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨_, hu, ?_⟩))
        unfold shiftX
        ext
        · show v.1 - (cut + 1) + (cut + 1) = v.1
          omega
        · rfl
    · -- consecutive vertices adjacent
      have hadj : Adjacent (cut, cutRow) (shiftX (cut + 1) b) := by
        rw [hb]
        unfold Adjacent shiftX
        simp
      have hchR' : chainAdjacent ((b :: restR).map (shiftX (cut + 1))) = true :=
        chainAdjacent_map_shiftX (cut + 1) (b :: restR) chR
      exact chainAdjacent_append pL (shiftX (cut + 1) b) (restR.map (shiftX (cut + 1)))
        (cut, cutRow) lastL chL hadj hchR'
end GridHam
