-- Prove2me | solution 1 for MatchingPolytope.Multi.sum_chi_inside
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:20:57.489888+00:00
-- url     : https://prove2.me/submissions/57bb260d-5701-42f1-9830-fd914ea20da6

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
    ∑ e ∈ inside ends D S, chi M e = ((inside ends M S).card : ℝ) := by
  classical
  simp only [chi]
  rw [Finset.sum_boole]
  congr 2
  ext e
  simp only [inside, Finset.mem_filter]
  constructor
  · rintro ⟨⟨-, h⟩, hm⟩; exact ⟨hm, h⟩
  · rintro ⟨hm, h⟩; exact ⟨⟨hM hm, h⟩, hm⟩
end MatchingPolytope.Multi
