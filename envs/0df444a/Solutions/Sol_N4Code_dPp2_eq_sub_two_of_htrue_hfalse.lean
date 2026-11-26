-- Prove2me | solution 1 for N4Code.dPp2_eq_sub_two_of_htrue_hfalse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:27:59.187797+00:00
-- url     : https://prove2.me/submissions/23e9fc01-d5ee-43f6-ad49-59b661f6901e

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
import Theorems.Thm_N4Code_dRow12_flip2_sub_two

set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂)
    (h1 : C t₁ = col1) (h7 : C t₂ = col7) (y : Word n)
    (hy1 : y t₁ = true) (hy2 : y t₂ = false) :
    dPp2 C t₁ t₂ y = dP C y - 2 := by
  have h12 := dRow12_flip2_sub_two C t₁ t₂ htne h1 h7 y hy1 hy2
  unfold dPp2 dP
  change dRow C 2 (flipTwoBits t₁ t₂ y) = dRow C 2 y - 2
  omega
end N4Code
