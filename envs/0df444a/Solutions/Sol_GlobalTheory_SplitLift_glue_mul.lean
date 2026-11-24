-- Prove2me | solution 1 for GlobalTheory.SplitLift.glue_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:09:36.96087+00:00
-- url     : https://prove2.me/submissions/c71f75a9-ec75-4cbf-9ad1-7decaf52e8ca

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ExistsReduction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsUnitaryStabilizerLiftOfSplitIdempotent
import Theorems.Thm_GlobalTheory_SplitLift_adj_mul
import Theorems.Thm_GlobalTheory_SplitLift_adj_smul
import Theorems.Thm_GlobalTheory_SplitLift_adj_one
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
theorem _root_.solution (s : A →+* A) {J : Matrix (Fin n) (Fin n) A} (hJ : IsUnit J.det) {e : A}
    (he : e * e = e) (hes : e * s e = 0) {X X' : Matrix (Fin n) (Fin n) A}
    (hX : e • X = X) (hX' : e • X' = X') (h : X * X' = e • (1 : Matrix (Fin n) (Fin n) A)) :
    glue s J e X X' * glue s J e X' X = 1 := by
  have hse : s e * s e = s e := by rw [← map_mul, he]
  have a1 : s e • adj s J X = adj s J X := by rw [← adj_smul, hX]
  have a2 : s e • adj s J X' = adj s J X' := by rw [← adj_smul, hX']
  have u1 : (1 - e - s e) * e = 0 := by linear_combination -he - hes
  have u2 : (1 - e - s e) * s e = 0 := by linear_combination -hse - hes
  have z1 : (1 - e - s e) • X = 0 := by rw [← hX, smul_smul, u1, zero_smul]
  have z2 : (1 - e - s e) • X' = 0 := by rw [← hX', smul_smul, u1, zero_smul]
  have z3 : (1 - e - s e) • adj s J X = 0 := by rw [← a1, smul_smul, u2, zero_smul]
  have z4 : (1 - e - s e) • adj s J X' = 0 := by rw [← a2, smul_smul, u2, zero_smul]
  have z5 : X * adj s J X = 0 := by
    rw [← a1]; nth_rewrite 1 [← hX]
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hes, zero_smul]
  have z6 : adj s J X' * X' = 0 := by
    rw [← a2]; nth_rewrite 2 [← hX']
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_comm, hes, zero_smul]
  have z7 : adj s J X' * adj s J X = s e • (1 : Matrix (Fin n) (Fin n) A) := by
    rw [adj_mul s hJ, h, adj_smul, adj_one s hJ]
  have u3 : (1 - e - s e) * (1 - e - s e) = 1 - e - s e := by linear_combination -u1 - u2
  simp only [glue, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.one_mul, Matrix.mul_one, smul_add, smul_smul, z1, z2, z3, z4, z5, z6, z7, h, u3]
  module
end GlobalTheory.SplitLift
