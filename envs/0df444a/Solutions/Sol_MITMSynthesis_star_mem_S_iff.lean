-- Prove2me | solution 1 for MITMSynthesis.star_mem_S_iff
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-11T07:26:03.524987+00:00
-- url     : https://prove2.me/submissions/830bb7aa-c987-4cdc-aa5b-79c143473172

import Mathlib
import Definitions.Def_MITMSynthesis_Gate
import Definitions.Def_MITMSynthesis_depthOneSet
import Definitions.Def_MITMSynthesis_S
import Theorems.Thm_MITMSynthesis_star_mem_depthOneSet

open MITMSynthesis

/-- Adjoint closure of every exact-depth search layer. The depth-one closure
is the already-proved platform theorem; reversing the layer list preserves
its length and implements the adjoint of its product. -/
theorem solution {n : ℕ} {G : Set Gate} (hG : IsInstructionSet G) (i : ℕ)
    (U : Matrix (Q n) (Q n) ℂ) :
    U ∈ star '' S (depthOneSet n G) i ↔ U ∈ S (depthOneSet n G) i := by
  have hprod (L : List (Matrix (Q n) (Q n) ℂ)) :
      (L.reverse.map star).prod = star L.prod := by
    induction L with
    | nil => simp
    | cons a L ih =>
      simpa [List.reverse_cons, List.map_append, List.prod_append, star_mul] using
        congrArg (fun M => M * star a) ih
  have hclosed (M : Matrix (Q n) (Q n) ℂ)
      (hM : M ∈ S (depthOneSet n G) i) : star M ∈ S (depthOneSet n G) i := by
    rcases hM with ⟨L, hlen, hL, rfl⟩
    refine ⟨L.reverse.map star, by simpa using hlen, ?_, hprod L⟩
    intro X hX
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hX
    exact star_mem_depthOneSet hG (hL x (by simpa using hx))
  constructor
  · rintro ⟨M, hM, rfl⟩
    exact hclosed M hM
  · intro hU
    exact ⟨star U, hclosed U hU, star_star U⟩
