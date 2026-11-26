-- Prove2me | solution 1 for N4Code.Z4_implies_htrue_hfalse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:21:53.278895+00:00
-- url     : https://prove2.me/submissions/aee63796-f715-4fa0-888d-4d3e70f1a0cc

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
import Theorems.Thm_N4Code_bool_ne_cases
import Theorems.Thm_N4Code_dO_le_dOp2_of_hfalse_htrue
import Theorems.Thm_N4Code_dP_add_two_of_hfalse_htrue

set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂)
    (h1 : C t₁ = col1) (h7 : C t₂ = col7) {y : Word n} (hy : Z4 C t₁ t₂ y) :
    y t₁ = true ∧ y t₂ = false := by
  rcases bool_ne_cases hy.1 with hyo | hyo
  · exact hyo
  · exfalso
    rcases hyo with ⟨hy1, hy2⟩
    have hO := dO_le_dOp2_of_hfalse_htrue C t₁ t₂ htne h1 h7 y hy1 hy2
    have hP := dP_add_two_of_hfalse_htrue C t₁ t₂ htne h1 h7 y hy1 hy2
    have hgt1 : dO C y > min (dP C y) (dPp2 C t₁ t₂ y) := hy.2.1
    have hgt2 : dP C y > min (dO C y) (dOp2 C t₁ t₂ y) := hy.2.2.1
    have hmin1 : min (dP C y) (dPp2 C t₁ t₂ y) = dP C y := by
      rw [← hP, min_eq_left]
      omega
    have hmin2 : min (dO C y) (dOp2 C t₁ t₂ y) = dO C y := by
      exact min_eq_left hO
    omega
end N4Code
