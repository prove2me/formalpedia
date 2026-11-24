-- Prove2me | solution 1 for GlobalTheory.KuennethOne.section_MM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:33:53.573899+00:00
-- url     : https://prove2.me/submissions/bdcf80ad-8dc4-43a3-aa3b-6369c9dca2a8

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
theorem _root_.solution {y : S ⟶ Y} (hy : y ≫ iY = 𝟙 S) {s : X ⟶ Z} (hs : s ≫ p = 𝟙 X)
    (hs' : s ≫ q = iX ≫ y) (U : ι → X.Opens) (W : Y.Opens) (e : ⊤ ≤ y ⁻¹ᵁ W) (i : ι)
    (O : Z.Opens) (hU : O ≤ p ⁻¹ᵁ U i) (hW : O ≤ q ⁻¹ᵁ W) (hO : U i ≤ s ⁻¹ᵁ O) (z) :
    (s.appLE O (U i) hO).hom (MM H U W i O hU hW z) =
      TensorProduct.rid _ _ ((evA y hy W e).toLinearMap.lTensor _ z) i := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]; rfl
  | tmul a b =>
    have h3 : U i ≤ (iX ≫ y) ⁻¹ᵁ W := le_top.trans (iX.preimage_mono e)
    rw [LinearMap.lTensor_tmul, MM_tmul, map_mul, TensorProduct.rid_tmul, Pi.smul_apply,
      Algebra.smul_def, mul_comm]
    exact congrArg₂ _ ((appLE_appLE s q _ hs' hW hO h3 b).trans
      (appLE_appLE iX y _ rfl e le_top h3 b).symm)
      (((appLE_appLE s p _ hs hU hO le_rfl (a i)).trans (id_appLE _ _)).trans (rs_self _ _))
  | add x y hx hy => simp only [map_add, hx, hy]; rfl
end GlobalTheory.KuennethOne
