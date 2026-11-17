-- Prove2me | solution 1 for N25.psiBar_ker
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:46:10.169053+00:00
-- url     : https://prove2.me/submissions/831ff281-1c56-44bf-ace8-7afcfb292816

import Mathlib
import Definitions.Def_N25_LocalKummerCharacter
import Theorems.Thm_N25_level25_subgroup_membership
import Definitions.Def_N25

namespace N25

/-- The quintic residue character has kernel H25. -/
theorem _root_.solution : psiBar.ker = H25 := by
  have hr : ∀ u : (ZMod 25)ˣ, psiBar u = 1 ↔
      (u : ZMod 25) = 1 ∨ (u : ZMod 25) = 7 ∨
      (u : ZMod 25) = 18 ∨ (u : ZMod 25) = 24 := by decide
  ext u
  rw [MonoidHom.mem_ker, level25_subgroup_membership]
  exact hr u

end N25
