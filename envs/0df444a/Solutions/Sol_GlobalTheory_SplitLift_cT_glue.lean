-- Prove2me | solution 1 for GlobalTheory.SplitLift.cT_glue
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:23:29.922904+00:00
-- url     : https://prove2.me/submissions/e2d55991-70bb-425f-807a-3bb3e6ad6a0e

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ExistsReduction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsUnitaryStabilizerLiftOfSplitIdempotent
import Theorems.Thm_GlobalTheory_SplitLift_cT_add
import Theorems.Thm_GlobalTheory_SplitLift_cT_smul
import Theorems.Thm_GlobalTheory_SplitLift_mul_adj
import Theorems.Thm_GlobalTheory_SplitLift_cT_adj_mul
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_GlobalTheory_RowLev_Red_map_one
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
theorem _root_.solution (s : A →+* A) (hs : ∀ a, s (s a) = a) {J : Matrix (Fin n) (Fin n) A}
    (hH : IsHerm s J) (hJ : IsUnit J.det) (e : A) (X X' : Matrix (Fin n) (Fin n) A) :
    cT s (glue s J e X X') * J = J * glue s J e X' X := by
  simp only [glue, cT_add, cT_smul, cT_one, Matrix.add_mul, Matrix.mul_add, cT_adj_mul s hs hH hJ,
    mul_adj s hJ, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, map_sub,
    map_one, hs]
  rw [sub_right_comm]
  abel
end GlobalTheory.SplitLift
