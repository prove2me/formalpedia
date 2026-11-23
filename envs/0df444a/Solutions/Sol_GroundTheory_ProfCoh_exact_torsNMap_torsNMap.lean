-- Prove2me | solution 1 for GroundTheory.ProfCoh.exact_torsNMap_torsNMap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:02:40.990561+00:00
-- url     : https://prove2.me/submissions/8474a8b8-3b4e-4e67-a5e4-515bf7e8f4be

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_AdditiveDefs
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_AdditiveSnake

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
universe u v
open Representation
variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] (n : ℕ)
variable {n} (f : A →+ B) (h : B →+ C) (hh : Function.Surjective h)
variable {f h}
variable (hfh : Function.Exact f h)
include hh hfh
variable (hf : Function.Injective f)
include hf
omit hh
namespace GroundTheory.ProfCoh
theorem _root_.solution : Function.Exact (torsNMap n f) (torsNMap n h) := by
  intro y
  constructor
  · intro hy
    obtain ⟨a, ha⟩ := (hfh (y : B)).1 (congrArg Subtype.val hy)
    refine ⟨⟨a, (mem_ker_lsmul_iff n a).2 (hf ?_)⟩, Subtype.ext ha⟩
    rw [map_nsmul, ha, map_zero]
    exact (mem_ker_lsmul_iff n (y : B)).1 y.2
  · rintro ⟨x, rfl⟩
    exact Subtype.ext ((hfh _).2 ⟨x, rfl⟩)
end GroundTheory.ProfCoh
