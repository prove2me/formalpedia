-- Prove2me | solution 2 for MarkovProcess.mem_image_val_iff
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T07:42:04.21973+00:00
-- url     : https://prove2.me/submissions/ae4efdd8-9964-4cb8-b8aa-071f5898671c

import Mathlib
open MeasureTheory
variable {alpha : Type*} (U : Set alpha)
theorem solution {C : Set U} {y : alpha} (hy : y ∈ U) :
    y ∈ Subtype.val '' C ↔ (⟨y, hy⟩ : U) ∈ C := by
  constructor
  · rintro ⟨⟨z, hz⟩, hC, rfl⟩; exact hC
  · intro h; exact ⟨_, h, rfl⟩
