-- Prove2me | solution 1 for N4Code.dRowMin_swapBit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:25:50.657388+00:00
-- url     : https://prove2.me/submissions/462f9ade-b887-464a-9cff-3118d93981e2

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
import Theorems.Thm_N4Code_dRow_swapBit

set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (S : Finset (Fin 4)) (hS : S.Nonempty)
    (t₁ t' : Fin n) (h1 : C t₁ = col0) (h' : C t' = col0) (y : Word n) :
    dRowMin C S hS (swapBits t₁ t' y) = dRowMin C S hS y := by
  unfold dRowMin
  have hcong : S.image (fun i => dRow C i (swapBits t₁ t' y)) = S.image (fun i => dRow C i y) := by
    apply Finset.image_congr
    intro i _
    exact dRow_swapBit C i t₁ t' h1 h' y
  simp [hcong]
end N4Code
