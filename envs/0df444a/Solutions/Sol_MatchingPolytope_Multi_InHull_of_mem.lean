-- Prove2me | solution 1 for MatchingPolytope.Multi.InHull.of_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:21:00.796355+00:00
-- url     : https://prove2.me/submissions/a67f40d5-2702-4da4-a969-0fe56d7035b5

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
variable [Fintype E]
namespace MatchingPolytope.Multi
namespace InHull
theorem _root_.solution {Q : Finset E → Prop} {M : Finset E} (hM : Q M) : InHull Q (chi M) := by
  classical
  refine ⟨fun N => if N = M then 1 else 0, fun N => by dsimp only; split_ifs <;> norm_num,
    fun N hN => ?_, by simp, by simp⟩
  dsimp only at hN
  split_ifs at hN with h
  · exact h ▸ hM
  · exact absurd rfl hN
end InHull
end MatchingPolytope.Multi
