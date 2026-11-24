-- Prove2me | solution 1 for GlobalTheory.SatakeWeyl.InclusionMultiplication.extendMatrixByIdentityAlongIndices_unitary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:21:11.910319+00:00
-- url     : https://prove2.me/submissions/c40b9014-be92-408f-9115-7f9a545613b1

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSmallerUnitaryGroupEmbedding
import Theorems.Thm_GlobalTheory_SatakeWeyl_InclusionMultiplication_antiJ_mul_incl
import Theorems.Thm_GlobalTheory_SatakeWeyl_InclusionMultiplication_inclT_mul_antiJ
import Theorems.Thm_GlobalTheory_SatakeWeyl_InclusionMultiplication_extendMatrixByIdentityAlongIndices_mul
import Theorems.Thm_GlobalTheory_SatakeWeyl_InclusionMultiplication_conjTranspose_extendMatrixByIdentityAlongIndices
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
import Theorems.Thm_GlobalTheory_UnitarySwap_antiJ_mul_self
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
theorem _root_.solution [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) {e : Fin r → Fin n} (he : Function.Injective e)
    (hr : ∀ i, e i.rev = (e i).rev) (M : Matrix (Fin r) (Fin r) L)
    (hM : cT σ M * antiJ L r * M = antiJ L r) :
    cT σ (ext1 e M) * antiJ L n * ext1 e M = antiJ L n := by
  have hJ : ∀ N : Matrix (Fin r) (Fin r) L, antiJ L n * ext1 e N
      = ext1 e (antiJ L r * N * antiJ L r) * antiJ L n := by
    intro N
    have h2 : antiJ L r * N * antiJ L r - 1 = antiJ L r * (N - 1) * antiJ L r := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, GlobalTheory.UnitarySwap.antiJ_mul_self]
    unfold ext1
    rw [h2, Matrix.mul_add, Matrix.add_mul, Matrix.one_mul, Matrix.mul_one, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, antiJ_mul_incl hr]
    simp only [Matrix.mul_assoc]
    rw [inclT_mul_antiJ hr, ← Matrix.mul_assoc (antiJ L r) (antiJ L r), GlobalTheory.UnitarySwap.antiJ_mul_self,
      Matrix.one_mul]
  rw [conjTranspose_extendMatrixByIdentityAlongIndices, Matrix.mul_assoc, hJ, ← Matrix.mul_assoc, ← extendMatrixByIdentityAlongIndices_mul he, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hM,
    GlobalTheory.UnitarySwap.antiJ_mul_self]
  simp [ext1]
end GlobalTheory.SatakeWeyl.InclusionMultiplication
