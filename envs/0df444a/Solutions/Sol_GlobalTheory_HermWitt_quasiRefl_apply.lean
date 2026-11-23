-- Prove2me | solution 1 for GlobalTheory.HermWitt.quasiRefl_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:54:19.4348+00:00
-- url     : https://prove2.me/submissions/59043e6b-aaa8-4d72-8453-9a2d9c1eaec7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsGlIsometryCompEqOfNondegenerate

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
theorem _root_.solution (B : V →ₗ[E] V →ₛₗ[c] E) (v : V) (a : E) (z : V) :
    quasiRefl B v a z = z - (a⁻¹ * B z v) • v := by
  simp [quasiRefl]
end GlobalTheory.HermWitt
