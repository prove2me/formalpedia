-- Prove2me | solution 1 for MatchingPolytope.Multi.sum_chi_gcut
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:20:15.53439+00:00
-- url     : https://prove2.me/submissions/90b21db9-c11a-4d0c-8347-bc2742333208

module
public import Mathlib
public import Definitions.Def_MatchingPolytope_Multigraph

set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope MatchingPolytope.Multi
open Finset
variable {V E : Type*}
variable {ends : E → Sym2 V} {W : Finset V} {F : Finset E}
namespace MatchingPolytope.Multi
theorem _root_.solution {M D : Finset E} (hM : M ⊆ D) (S : Finset V) :
    ∑ e ∈ gcut ends D S, chi M e = ((gcut ends M S).card : ℝ) := by
  classical
  simp only [chi]
  rw [Finset.sum_boole]
  congr 2
  ext e
  simp only [gcut, Finset.mem_filter]
  constructor
  · rintro ⟨⟨-, h⟩, hm⟩; exact ⟨hm, h⟩
  · rintro ⟨hm, h⟩; exact ⟨⟨hM hm, h⟩, hm⟩
end MatchingPolytope.Multi
