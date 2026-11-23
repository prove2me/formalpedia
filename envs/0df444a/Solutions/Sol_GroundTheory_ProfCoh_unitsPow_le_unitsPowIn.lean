-- Prove2me | solution 1 for GroundTheory.ProfCoh.unitsPow_le_unitsPowIn
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:03:05.479582+00:00
-- url     : https://prove2.me/submissions/17c7fff1-8f1c-42ff-b977-08d57818f38e

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_KummerBasic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.ProfCoh
open Polynomial
variable (K : Type*) [Field K] (n : ℕ)
variable (L : Type*) [Field L] [Algebra K L]
namespace GroundTheory.ProfCoh
theorem _root_.solution : unitsPow K n ≤ unitsPowIn K n L := by
  intro a ha
  obtain ⟨b, rfl⟩ := mem_unitsPow.mp ha
  exact mem_unitsPowIn.mpr ⟨algebraMap K L b, by simp⟩
end GroundTheory.ProfCoh
