-- Prove2me | solution 1 for GlobalTheory.KuennethOne.MM_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:40:37.624317+00:00
-- url     : https://prove2.me/submissions/d3a2f784-af65-4769-b77d-7fd68c200499

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitsOfIsAffineOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_MemRangeRTensorOfForallDual
import Theorems.Thm_GlobalTheory_KuennethOne_MM_tmul
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
theorem _root_.solution [Fintype ι] [DecidableEq ι] (U : ι → X.Opens) (W : Y.Opens) (i : ι) (O : Z.Opens)
    (hU : O ≤ p ⁻¹ᵁ U i) (hW : O ≤ q ⁻¹ᵁ W) (z) :
    MM H U W i O hU hW z = mm H (U i) W O hU hW (TensorProduct.piLeft _ _ _ z i) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero, Pi.zero_apply]; rfl
  | tmul x y => rw [MM_tmul]; simp [mm]; rfl
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]; rfl
end GlobalTheory.KuennethOne
