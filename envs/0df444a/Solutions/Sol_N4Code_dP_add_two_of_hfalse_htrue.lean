-- Prove2me | solution 1 for N4Code.dP_add_two_of_hfalse_htrue
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:21:11.140377+00:00
-- url     : https://prove2.me/submissions/e8a0bdcd-c1ed-47b7-a475-9c7e78f1dd47

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
import Theorems.Thm_N4Code_dRow12_flip2_add_two

set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂)
    (h1 : C t₁ = col1) (h7 : C t₂ = col7) (y : Word n)
    (hy1 : y t₁ = false) (hy2 : y t₂ = true) :
    dP C y + 2 = dPp2 C t₁ t₂ y := by
  unfold dPp2 dP
  exact (dRow12_flip2_add_two C t₁ t₂ htne h1 h7 y hy1 hy2).2.symm
end N4Code
