-- Prove2me | solution 1 for GroundTheory.ProfCoh.Supernatural.dvd_iff_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:09:56.2191+00:00
-- url     : https://prove2.me/submissions/b55335c0-72b0-49f2-afcf-f180c6ba0602

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_Supernatural
import Theorems.Thm_GroundTheory_ProfCoh_Supernatural_le_def

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
open GroundTheory.ProfCoh.Supernatural
namespace GroundTheory.ProfCoh.Supernatural
theorem _root_.solution {a b : Supernatural} : a ∣ b ↔ a ≤ b := by
  constructor
  · rintro ⟨c, rfl⟩
    rw [le_def]
    intro p
    simp
  · intro h
    refine ⟨mk fun p => b.exp p - a.exp p, ?_⟩
    ext p
    simp [add_tsub_cancel_of_le (le_def.mp h p)]
end GroundTheory.ProfCoh.Supernatural
