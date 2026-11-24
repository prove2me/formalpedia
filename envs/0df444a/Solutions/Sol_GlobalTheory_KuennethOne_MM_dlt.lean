-- Prove2me | solution 1 for GlobalTheory.KuennethOne.MM_dlt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:50:20.254952+00:00
-- url     : https://prove2.me/submissions/7d5d90c3-a0e1-4110-a63c-26843f2d0f6f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitsOfIsAffineOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_MemRangeRTensorOfForallDual
import Theorems.Thm_GlobalTheory_KuennethOne_MM_tmul
import Theorems.Thm_GlobalTheory_KuennethOne_dlt_apply
import Theorems.Thm_GlobalTheory_KuennethOne_appLE_rs
import Theorems.Thm_GlobalTheory_KuennethOne_rs_appLE
import Theorems.Thm_GlobalTheory_KuennethOne_rs_rs
import Theorems.Thm_GlobalTheory_KuennethOne_rs_self
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.KuennethOne.appLE_rs
attribute [local simp] GlobalTheory.KuennethOne.rs_appLE
attribute [local simp] GlobalTheory.KuennethOne.rs_rs
attribute [local simp] GlobalTheory.KuennethOne.rs_self



set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace TensorProduct
open GlobalTheory GlobalTheory.KuennethOne
variable {S X Y Z T : Scheme.{0}}
variable {p : Z ⟶ X} {q : Z ⟶ Y} {iX : X ⟶ S} {iY : Y ⟶ S} (H : IsPullback p q iX iY)
variable {ι : Type}
namespace GlobalTheory.KuennethOne
theorem _root_.solution (U : ι → X.Opens) (W : Y.Opens) (k : ι × ι) (O : Z.Opens)
    (hU : O ≤ p ⁻¹ᵁ (U k.1 ⊓ U k.2)) (hW : O ≤ q ⁻¹ᵁ W) (z) :
    MM H (fun k : ι × ι => U k.1 ⊓ U k.2) W k O hU hW ((dlt iX U).rTensor _ z) =
      MM H U W k.1 O (hU.trans (p.preimage_mono inf_le_left)) hW z -
        MM H U W k.2 O (hU.trans (p.preimage_mono inf_le_right)) hW z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero, sub_zero]
  | tmul x y =>
    rw [LinearMap.rTensor_tmul, MM_tmul, MM_tmul, MM_tmul, dlt_apply, map_sub, sub_mul]
    exact congrArg₂ _ (congrArg (· * _) (appLE_rs p _ hU _)) (congrArg (· * _) (appLE_rs p _ hU _))
  | add x y hx hy => simp only [map_add, hx, hy]; ring
end GlobalTheory.KuennethOne
