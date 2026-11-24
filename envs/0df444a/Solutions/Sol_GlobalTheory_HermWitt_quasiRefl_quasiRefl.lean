-- Prove2me | solution 1 for GlobalTheory.HermWitt.quasiRefl_quasiRefl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:15:37.00782+00:00
-- url     : https://prove2.me/submissions/6254feea-0ef0-4e4e-9efe-bda26cbd4a5d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsGlIsometryCompEqOfNondegenerate
import Theorems.Thm_GlobalTheory_HermWitt_quasiRefl_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.HermWitt
open Module Matrix GlobalTheory.HermDiag
variable {E : Type*} [Field E] {c : E →+* E} {V : Type*} [AddCommGroup V] [Module E V]
namespace GlobalTheory.HermWitt
theorem _root_.solution (B : V →ₗ[E] V →ₛₗ[c] E) {v : V} {a b : E} (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : a + b = B v v) (z : V) : quasiRefl B v b (quasiRefl B v a z) = z := by
  rw [quasiRefl_apply, quasiRefl_apply, LinearMap.map_sub₂, LinearMap.map_smul₂, ← hab, sub_sub,
    ← add_smul, smul_eq_mul]
  have : a⁻¹ * B z v + b⁻¹ * (B z v - a⁻¹ * B z v * (a + b)) = 0 := by
    field_simp
    ring
  rw [this, zero_smul, sub_zero]
end GlobalTheory.HermWitt
