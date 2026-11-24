-- Prove2me | solution 1 for GlobalTheory.SatakeWeyl.InclusionMultiplication.conjTranspose_extendMatrixByIdentityAlongIndices
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:31:20.034946+00:00
-- url     : https://prove2.me/submissions/7b226da7-6883-4919-a27f-f99049676e58

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSmallerUnitaryGroupEmbedding
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open Formalism.UG GlobalTheory.SatakeWeyl
open Matrix
open GlobalTheory GlobalTheory.SatakeWeyl GlobalTheory.SatakeWeyl.InclusionMultiplication
variable {L : Type} [Field L] {n r : ℕ}
namespace GlobalTheory.SatakeWeyl.InclusionMultiplication
theorem _root_.solution (σ : L →+* L) (e : Fin r → Fin n) (M : Matrix (Fin r) (Fin r) L) :
    cT σ (ext1 e M) = ext1 e (cT σ M) := by
  ext a b
  simp only [cT, ext1, Matrix.transpose_apply, Matrix.map_apply, Matrix.add_apply, Matrix.mul_apply, map_add,
    map_sum, map_mul, incl, Matrix.of_apply, Matrix.sub_apply, map_sub, Matrix.one_apply, apply_ite σ, map_one,
    map_zero, Finset.sum_mul]
  congr 1
  · simp only [eq_comm]
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [eq_comm (a := i) (b := j)]
    ring
end GlobalTheory.SatakeWeyl.InclusionMultiplication
