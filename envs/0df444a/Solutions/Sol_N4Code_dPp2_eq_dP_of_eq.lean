-- Prove2me | solution 1 for N4Code.dPp2_eq_dP_of_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:26:53.770045+00:00
-- url     : https://prove2.me/submissions/b42d2ca1-6843-4b88-8e2e-2739ac065508

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
import Theorems.Thm_N4Code_dRow12_flip2_eq_of_eq

set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂)
    (h1 : C t₁ = col1) (h7 : C t₂ = col7) (y : Word n) (hyeq : y t₁ = y t₂) :
    dPp2 C t₁ t₂ y = dP C y := by
  unfold dPp2 dP
  exact (dRow12_flip2_eq_of_eq C t₁ t₂ htne h1 h7 y hyeq).2
end N4Code
