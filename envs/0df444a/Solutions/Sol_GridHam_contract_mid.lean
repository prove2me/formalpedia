-- Prove2me | solution 1 for GridHam.contract_mid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:43:58.700074+00:00
-- url     : https://prove2.me/submissions/21ff4a62-330c-41ca-878b-3285ff98f4ee

module
public import Definitions.Def_GridHam_StripSplit
public import Definitions.Def_GridHam_F3
public import Theorems.Thm_GridHam_nodup_remove_mid
public import Theorems.Thm_P2M_GridHam_head__map_of_95c870c06cfa
public import Theorems.Thm_GridHam_chainAdjacent_cons
public import Theorems.Thm_GridHam_chainAdjacent_map_on
public import Theorems.Thm_GridHam_chainAdjacent_replace_tail
public import Theorems.Thm_GridHam_chainAdjacent_suffix
public import Theorems.Thm_GridHam_mem_allCoords
public import Theorems.Thm_GridHam_mem_insert_iff
public import Theorems.Thm_GridHam_nodup_map_coord_on
public import Theorems.Thm_P2M_GridHam_getLast__append_cons_527000d4767a
public import Theorems.Thm_P2M_GridHam_getLast__map_coord_39a438577d66


set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution (w : ℕ) (u v a b : Coord) (L M R : List Coord)
    (hM : ∀ c : Coord, c.1 < 2 → c.2 < 3 → c ∈ M) (hMx : ∀ c ∈ M, c.1 < 2)
    (hMl : M.length = 6) (hab : Adjacent a b)
    (hvp : ValidPath w 3 u v (L ++ a :: (M ++ b :: R))) :
    ValidPath (w - 2) 3 (shiftL2 u) (shiftL2 v) ((L ++ a :: b :: R).map shiftL2) := by
  obtain ⟨hlen, hhead, hlast, hnd, hin, hcov, hch⟩ := hvp
  obtain ⟨hndQ, hdis⟩ := nodup_remove_mid L a b M R hnd
  have hsubQ : ∀ c ∈ L ++ a :: b :: R, c ∈ L ++ a :: (M ++ b :: R) :=
    fun c hc => (mem_insert_iff c L M R a b).mpr (Or.inr hc)
  have hge : ∀ c ∈ L ++ a :: b :: R, 2 ≤ c.1 := by
    intro c hc
    by_contra hlt
    have hcb := hin c (hsubQ c hc)
    unfold InBounds at hcb
    exact hdis c (hM c (by omega) hcb.2) hc
  have ha2 : 2 ≤ a.1 := hge a (by simp)
  have haw := hin a (hsubQ a (by simp))
  unfold InBounds at haw
  unfold ValidPath
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [List.length_map]
    simp only [List.length_append, List.length_cons] at hlen ⊢
    omega
  · have e : (L ++ a :: b :: R).head? = (L ++ a :: (M ++ b :: R)).head? := by
      cases L <;> rfl
    exact head?_map_of shiftL2 _ u (e.trans hhead)
  · have e1 : (L ++ a :: b :: R).getLast? = (b :: R).getLast? :=
      (getLast?_append_cons L a (b :: R)).trans rfl
    have e2 : (L ++ a :: (M ++ b :: R)).getLast? = (b :: R).getLast? :=
      (getLast?_append_cons L a (M ++ b :: R)).trans (getLast?_append_cons (a :: M) b R)
    exact getLast?_map_coord shiftL2 _ v (e1.trans (e2.symm.trans hlast))
  · apply nodup_map_coord_on shiftL2 _ _ hndQ
    intro c hc d hd hcd
    have hc2 := hge c hc
    have hd2 := hge d hd
    unfold shiftL2 at hcd
    have h1 := congrArg Prod.fst hcd
    have h2 := congrArg Prod.snd hcd
    dsimp only at h1 h2
    ext
    · omega
    · omega
  · intro c hc
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
    have hdb := hin d (hsubQ d hd)
    have hd2 := hge d hd
    unfold InBounds at hdb ⊢
    unfold shiftL2
    dsimp only
    exact ⟨by omega, hdb.2⟩
  · intro c hc
    obtain ⟨hcx, hcy⟩ := (mem_allCoords (w - 2) 3 c).mp hc
    have hd := hcov (c.1 + 2, c.2) ((mem_allCoords w 3 _).mpr ⟨by dsimp only; omega, hcy⟩)
    rcases (mem_insert_iff _ L M R a b).mp hd with hdM | hdQ
    · have := hMx _ hdM
      dsimp only at this
      omega
    · refine List.mem_map.mpr ⟨_, hdQ, ?_⟩
      unfold shiftL2
      ext
      · show c.1 + 2 - 2 = c.1
        omega
      · rfl
  · have hbR : chainAdjacent (b :: R) = true :=
      chainAdjacent_suffix (L ++ a :: M) (b :: R) (by simpa using hch)
    have habR : chainAdjacent (a :: b :: R) = true := chainAdjacent_cons a b (b :: R) rfl hab hbR
    have hQ := chainAdjacent_replace_tail L a (M ++ b :: R) (b :: R) hch habR
    apply chainAdjacent_map_on shiftL2 _ _ hQ
    intro x hx y hy hadj
    have hx2 := hge x hx
    have hy2 := hge y hy
    unfold Adjacent at hadj ⊢
    unfold shiftL2
    dsimp only
    omega
end GridHam
