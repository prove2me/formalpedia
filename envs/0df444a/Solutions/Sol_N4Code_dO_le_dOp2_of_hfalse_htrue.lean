-- Prove2me | solution 1 for N4Code.dO_le_dOp2_of_hfalse_htrue
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:21:15.521292+00:00
-- url     : https://prove2.me/submissions/07127757-59d6-4b52-95e4-b453c8b3ce38

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
import Theorems.Thm_N4Code_dRow12_flip2_add_two
import Theorems.Thm_N4Code_dRow03_flip2_eq_ne

set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂)
    (h1 : C t₁ = col1) (h7 : C t₂ = col7) (y : Word n)
    (hy1 : y t₁ = false) (hy2 : y t₂ = true) :
    dO C y ≤ dOp2 C t₁ t₂ y := by
  have h03 := dRow03_flip2_eq_ne C t₁ t₂ htne h1 h7 y (by simp [hy1, hy2])
  have h12 := dRow12_flip2_add_two C t₁ t₂ htne h1 h7 y hy1 hy2
  unfold dOp2 dO
  change min (dRow C 0 y) (min (dRow C 1 y) (dRow C 3 y)) ≤
    min (dRow C 0 (flipTwoBits t₁ t₂ y))
      (min (dRow C 1 (flipTwoBits t₁ t₂ y)) (dRow C 3 (flipTwoBits t₁ t₂ y)))
  rw [h03.1, h03.2]
  have hle : dRow C 1 y ≤ dRow C 1 (flipTwoBits t₁ t₂ y) := by omega
  exact min_le_min le_rfl (min_le_min hle le_rfl)
end N4Code
