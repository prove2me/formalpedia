-- Prove2me | solution 1 for GlobalTheory.Glue.IsNTr.apply_eq_of_mem_adjoin
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:33:09.116351+00:00
-- url     : https://prove2.me/submissions/9101c63b-296f-4c05-a0aa-c054da62de82

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_EeProd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_ApplyEqOfMemAdjoin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped MatrixGroups
open GlobalTheory GlobalTheory.Glue
open GlobalTheory.KZ GlobalTheory.K5
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}
variable {p : ℕ} [Fact p.Prime] {Ωl : Type} [Field Ωl] [Algebra (O0 p) Ωl]
namespace GlobalTheory.Glue
namespace IsNTr
theorem _root_.solution {z F : Ω} (hF : F ∈ IntermediateField.adjoin ℚ {z}) {s t : Ω ≃ₐ[ℚ] Ω} (h : s z = t z) :
    s F = t F := by
  induction hF using IntermediateField.adjoin_induction with
  | mem x hx => rw [Set.mem_singleton_iff.1 hx, h]
  | algebraMap r => rw [AlgEquiv.commutes, AlgEquiv.commutes]
  | add x y _ _ hx hy => rw [map_add, map_add, hx, hy]
  | inv x _ hx => rw [map_inv₀, map_inv₀, hx]
  | mul x y _ _ hx hy => rw [map_mul, map_mul, hx, hy]
end IsNTr
end GlobalTheory.Glue
