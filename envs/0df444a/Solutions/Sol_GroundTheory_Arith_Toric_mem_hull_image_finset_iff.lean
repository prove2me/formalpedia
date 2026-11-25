-- Prove2me | solution 1 for GroundTheory.Arith.Toric.mem_hull_image_finset_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:29:32.786731+00:00
-- url     : https://prove2.me/submissions/2ad5caf2-c5c6-4542-91f9-8e8485f654ab

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_ExistsDualNegOfNotMemHullFinset
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_Lattice
import Theorems.Thm_GroundTheory_Arith_Toric_mem_hull_insert


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Toric
open Module PointedCone TensorProduct
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {E : Type*} [AddCommGroup E] [Module 𝕜 E]
namespace GroundTheory.Arith.Toric
theorem _root_.solution {ι : Type*} [DecidableEq ι] (T : Finset ι) (v : ι → E)
    {x : E} : x ∈ hull 𝕜 (v '' T) ↔ ∃ c : ι → 𝕜, (∀ i, 0 ≤ c i) ∧ ∑ i ∈ T, c i • v i = x := by
  induction T using Finset.induction_on generalizing x with
  | empty =>
    simp only [Finset.coe_empty, Set.image_empty, Submodule.span_empty, Submodule.mem_bot,
      Finset.sum_empty]
    constructor
    · rintro rfl; exact ⟨0, fun _ => le_rfl, rfl⟩
    · rintro ⟨_, _, rfl⟩; rfl
  | insert a T ha ih =>
    rw [Finset.coe_insert, Set.image_insert_eq, mem_hull_insert]
    constructor
    · rintro ⟨c, hc, y, hy, rfl⟩
      obtain ⟨d, hd, rfl⟩ := ih.1 hy
      refine ⟨Function.update d a c, fun i => ?_, ?_⟩
      · by_cases h : i = a
        · subst h; simpa using hc
        · simpa [h] using hd i
      · rw [Finset.sum_insert ha, Function.update_self]
        congr 1
        exact Finset.sum_congr rfl fun i hi => by
          rw [Function.update_of_ne (ne_of_mem_of_not_mem hi ha)]
    · rintro ⟨c, hc, rfl⟩
      rw [Finset.sum_insert ha]
      exact ⟨c a, hc a, _, ih.2 ⟨c, hc, rfl⟩, rfl⟩
end GroundTheory.Arith.Toric
