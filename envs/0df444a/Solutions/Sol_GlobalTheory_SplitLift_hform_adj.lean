-- Prove2me | solution 1 for GlobalTheory.SplitLift.hform_adj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:09:37.800913+00:00
-- url     : https://prove2.me/submissions/6ea5a58e-1b35-4c58-8a70-16eaf423ef19

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ExistsReduction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsUnitaryStabilizerLiftOfSplitIdempotent
import Theorems.Thm_GlobalTheory_SplitLift_mul_adj
import Theorems.Thm_GlobalTheory_SplitLift_hform_dot
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical
open GlobalTheory GlobalTheory.SplitLift
open Formalism.UG
variable {A : Type} [CommRing A] {n : ℕ}
namespace GlobalTheory.SplitLift
theorem _root_.solution (s : A →+* A) {J : Matrix (Fin n) (Fin n) A} (hJ : IsUnit J.det)
    (X : Matrix (Fin n) (Fin n) A) (x y : Fin n → A) :
    hform s J x (adj s J X *ᵥ y) = hform s J (X *ᵥ x) y := by
  rw [hform_dot, hform_dot, Matrix.mulVec_mulVec, mul_adj s hJ, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec]
  congr 1
  ext i
  simp [cT, Matrix.vecMul, Matrix.mulVec, dotProduct, map_sum, mul_comm]
end GlobalTheory.SplitLift
