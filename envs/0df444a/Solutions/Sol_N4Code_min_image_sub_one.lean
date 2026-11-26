-- Prove2me | solution 1 for N4Code.min_image_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:11:49.350864+00:00
-- url     : https://prove2.me/submissions/efeda04b-f15e-4ddd-9358-40b7abfe8358

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn

set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000
namespace N4Code
theorem _root_.solution {α : Type*} {S : Finset α} {f : α → ℕ} (hS : S.Nonempty) :
    (S.image (fun a => f a - 1)).min' (hS.image (fun a => f a - 1)) =
      (S.image f).min' (hS.image f) - 1 := by
  apply le_antisymm
  · have hm : (S.image f).min' (hS.image f) ∈ S.image f := Finset.min'_mem _ _
    rcases (Finset.mem_image.mp hm) with ⟨a, ha, hfa⟩
    have hmem : (fun a => f a - 1) a ∈ S.image (fun a => f a - 1) :=
      Finset.mem_image.mpr ⟨a, ha, rfl⟩
    have hle : (S.image (fun a => f a - 1)).min' (hS.image (fun a => f a - 1)) ≤ f a - 1 :=
      Finset.min'_le (S.image (fun a => f a - 1)) (f a - 1) hmem
    rwa [hfa] at hle
  · apply Finset.le_min'
    intro b hb
    rcases (Finset.mem_image.mp hb) with ⟨a, ha, hba⟩
    have hle : (S.image f).min' (hS.image f) ≤ f a :=
      Finset.min'_le (S.image f) (f a) (Finset.mem_image.mpr ⟨a, ha, rfl⟩)
    rw [← hba]
    exact Nat.sub_le_sub_right hle 1
end N4Code
