-- Prove2me | solution 1 for MarkovProcess.mem_image_val_iff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T07:41:13.096931+00:00
-- url     : https://prove2.me/submissions/928a34db-bc52-498c-a8e9-14e133c22d3e

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
variable {alpha : Type*} (U : Set alpha)

theorem solution {C : Set U} {y : alpha} (hy : y ∈ U) :
    y ∈ Subtype.val '' C ↔ (⟨y, hy⟩ : U) ∈ C := by
  rw [Subtype.coe_image, Set.mem_ofPred_eq]
  exact ⟨fun h ↦ h.choose_spec, fun h ↦ ⟨hy, h⟩⟩
