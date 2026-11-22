-- Prove2me | solution 1 for GridHam.extend_right_up
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:35:05.654696+00:00
-- url     : https://prove2.me/submissions/6aedce86-ea17-42ca-a518-7512bdb05e64

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_StripSplit
public import Theorems.Thm_GridHam_mem_allCoords
public import Theorems.Thm_P2M_GridHam_getLast__append_cons_527000d4767a
public import Theorems.Thm_GridHam_chainAdjacent_suffix
public import Theorems.Thm_GridHam_chainAdjacent_replace_tail
public import Theorems.Thm_GridHam_mem_insert_iff
public import Theorems.Thm_GridHam_nodup_insert
public import Theorems.Thm_GridHam_mem_rightDetour
public import Theorems.Thm_GridHam_rightDetour_length
public import Theorems.Thm_GridHam_rightDetour_nodup
public import Theorems.Thm_GridHam_chain_detour

set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution (w h : ℕ) (s t : Coord) (l1 l2 : List Coord) (y : ℕ) (hw : 1 ≤ w)
    (hv : ValidPath w h s t (l1 ++ (w - 1, y) :: (w - 1, y + 1) :: l2)) :
    ValidPath (w + 2) h s t (l1 ++ (w - 1, y) :: (rightDetour w h y ++ (w - 1, y + 1) :: l2)) := by
  obtain ⟨hlen, hhead, hlast, hnd, hin, hcov, hch⟩ := hv
  have hbin := hin (w - 1, y + 1) (by simp)
  unfold InBounds at hbin
  dsimp only at hbin
  have hy : y + 1 < h := hbin.2
  unfold ValidPath
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- length
    have e : (l1 ++ (w - 1, y) :: (rightDetour w h y ++ (w - 1, y + 1) :: l2)).length =
        (l1 ++ (w - 1, y) :: (w - 1, y + 1) :: l2).length + (rightDetour w h y).length := by
      simp only [List.length_append, List.length_cons]
      omega
    rw [e, hlen, rightDetour_length w h y hy, Nat.add_mul]
  · -- head
    have e : (l1 ++ (w - 1, y) :: (rightDetour w h y ++ (w - 1, y + 1) :: l2)).head? =
        (l1 ++ (w - 1, y) :: (w - 1, y + 1) :: l2).head? := by
      cases l1 <;> rfl
    exact e.trans hhead
  · -- last
    have e1 : (l1 ++ (w - 1, y) :: (rightDetour w h y ++ (w - 1, y + 1) :: l2)).getLast? =
        ((w - 1, y + 1) :: l2).getLast? :=
      (getLast?_append_cons l1 (w - 1, y) (rightDetour w h y ++ (w - 1, y + 1) :: l2)).trans
        (getLast?_append_cons ((w - 1, y) :: rightDetour w h y) (w - 1, y + 1) l2)
    have e2 : (l1 ++ (w - 1, y) :: (w - 1, y + 1) :: l2).getLast? =
        ((w - 1, y + 1) :: l2).getLast? :=
      (getLast?_append_cons l1 (w - 1, y) ((w - 1, y + 1) :: l2)).trans rfl
    exact e1.trans (e2.symm.trans hlast)
  · -- no repeats
    apply nodup_insert _ (rightDetour_nodup w h y hy) l1 _ _ l2 hnd
    intro u hu hm
    rw [mem_rightDetour w h y hy] at hu
    have hu' := hin u hm
    unfold InBounds at hu'
    omega
  · -- in bounds
    intro u hu
    rcases (mem_insert_iff u l1 _ l2 _ _).mp hu with hd | hp
    · rw [mem_rightDetour w h y hy] at hd
      unfold InBounds
      omega
    · have hu' := hin u hp
      unfold InBounds at hu' ⊢
      omega
  · -- coverage
    intro v hv
    obtain ⟨hvx, hvy⟩ := (mem_allCoords (w + 2) h v).mp hv
    by_cases hc : v.1 < w
    · exact (mem_insert_iff v l1 _ l2 _ _).mpr
        (Or.inr (hcov v ((mem_allCoords w h v).mpr ⟨hc, hvy⟩)))
    · exact (mem_insert_iff v l1 _ l2 _ _).mpr
        (Or.inl ((mem_rightDetour w h y hy v).mpr (by omega)))
  · -- adjacency
    have hb : chainAdjacent ((w - 1, y + 1) :: l2) = true :=
      chainAdjacent_suffix (l1 ++ [(w - 1, y)]) _ (by simpa using hch)
    exact chainAdjacent_replace_tail l1 (w - 1, y) ((w - 1, y + 1) :: l2) _ hch
      (chain_detour w h y hw hy l2 hb)
end GridHam
