-- Prove2me | solution 1 for MatchingPolytope.Multi.shrink_valid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:25:39.559585+00:00
-- url     : https://prove2.me/submissions/d2202172-31ff-4907-b133-6480d168d1e2

module
public import Definitions.Def_MatchingPolytope_Multigraph
public import Definitions.Def_MatchingPolytope_Shrink
public import Theorems.Thm_MatchingPolytope_Multi_mem_shrinkF
public import Theorems.Thm_MatchingPolytope_Multi_shrinkEnds_pair
public import Theorems.Thm_MatchingPolytope_Multi_Valid_pair


set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope MatchingPolytope.Multi
open Finset
variable {V E : Type*}
variable [DecidableEq V]
variable {ends : E → Sym2 V} {W : Finset V} {F : Finset E}
namespace MatchingPolytope.Multi
theorem _root_.solution (hV : Valid ends W F) {R : Finset V} {r : V} (hr : r ∈ R) :
    Valid (shrinkEnds ends R r) (shrinkW W R r) (shrinkF ends F R) := by
  constructor
  · intro e he u hu
    obtain ⟨heF, -⟩ := mem_shrinkF.1 he
    obtain ⟨a, b, -, ha, hb, h⟩ := hV.pair heF
    rw [shrinkEnds_pair h, Sym2.mem_iff] at hu
    simp only [shrinkW, Finset.mem_insert, Finset.mem_sdiff]
    rcases hu with rfl | rfl <;> simp only [collapse] <;> split_ifs <;> simp [*]
  · intro e he
    obtain ⟨heF, u, hu, huR⟩ := mem_shrinkF.1 he
    obtain ⟨a, b, hab, -, -, h⟩ := hV.pair heF
    rw [shrinkEnds_pair h, Sym2.mk_isDiag_iff]
    rw [h, Sym2.mem_iff] at hu
    simp only [collapse]
    rcases hu with rfl | rfl
    · simp only [huR, ↓reduceIte]
      split_ifs with hb
      · rintro rfl; exact huR hr
      · exact hab
    · simp only [huR, ↓reduceIte]
      split_ifs with ha
      · rintro rfl; exact huR hr
      · exact hab
end MatchingPolytope.Multi
