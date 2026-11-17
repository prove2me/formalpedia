-- Prove2me | solution 1 for N25.level25_subgroup_membership
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:41:00.029776+00:00
-- url     : https://prove2.me/submissions/cb4fc41f-f68d-4fe1-bd75-94f344bc203d

import Mathlib
import Definitions.Def_N25

set_option autoImplicit false

namespace N25

/-- The level subgroup consists of the four powers of seven. -/
theorem _root_.solution (u : (ZMod 25)ˣ) :
    u ∈ H25 ↔ (u : ZMod 25) = 1 ∨ (u : ZMod 25) = 7 ∨
      (u : ZMod 25) = 18 ∨ (u : ZMod 25) = 24 := by
  let K : Subgroup (ZMod 25)ˣ :=
    { carrier := {v | (v : ZMod 25) = 1 ∨ (v : ZMod 25) = 7 ∨
          (v : ZMod 25) = 18 ∨ (v : ZMod 25) = 24}
      one_mem' := by decide
      mul_mem' := by decide +kernel
      inv_mem' := by decide +kernel }
  have h : H25 = K := by
    apply le_antisymm
    · apply Subgroup.zpowers_le.mpr
      change (7 : ZMod 25) = 1 ∨ (7 : ZMod 25) = 7 ∨
        (7 : ZMod 25) = 18 ∨ (7 : ZMod 25) = 24
      decide
    · intro v hv
      rcases hv with h | h | h | h
      · have hv1 : v = 1 := Units.ext h
        simpa [hv1] using H25.one_mem
      · have hv7 : v = ZMod.unitOfCoprime 7 (by decide) := Units.ext h
        subst v
        exact Subgroup.mem_zpowers _
      · have hv18 : v = (ZMod.unitOfCoprime 7 (by decide)) ^ 3 :=
          Units.ext (h.trans (by decide))
        subst v
        exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
      · have hv24 : v = (ZMod.unitOfCoprime 7 (by decide)) ^ 2 :=
          Units.ext (h.trans (by decide))
        subst v
        exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
  rw [h]
  rfl

end N25
