-- Prove2me | solution 1 for N4Code.min_image_add_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:16:24.755169+00:00
-- url     : https://prove2.me/submissions/28a42fb4-1b5a-4ba1-bc60-d333c647172e

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
import Theorems.Thm_N4Code_min_image_sub_one

set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000
namespace N4Code
theorem _root_.solution {α : Type*} {S : Finset α} {f : α → ℕ} (hS : S.Nonempty) :
    (S.image (fun a => f a + 1)).min' (hS.image (fun a => f a + 1)) =
      (S.image f).min' (hS.image f) + 1 := by
  have h := min_image_sub_one (S := S) (f := fun a => f a + 1) hS
  have hcong : (S.image (fun a => (f a + 1) - 1)) = S.image f := by
    apply Finset.image_congr
    intro a _
    simp
  have h' : (S.image (fun a => f a + 1)).min' (hS.image (fun a => f a + 1)) - 1 =
      (S.image f).min' (hS.image f) := by
    simpa [hcong] using h.symm
  have hA : 0 < (S.image (fun a => f a + 1)).min' (hS.image (fun a => f a + 1)) := by
    rw [Finset.lt_min'_iff]
    intro y hy
    rcases (Finset.mem_image.mp hy) with ⟨a, ha, rfl⟩
    omega
  omega
end N4Code
