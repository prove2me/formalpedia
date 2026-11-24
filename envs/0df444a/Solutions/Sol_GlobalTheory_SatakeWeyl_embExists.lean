-- Prove2me | solution 1 for GlobalTheory.SatakeWeyl.embExists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:35:18.205825+00:00
-- url     : https://prove2.me/submissions/323857ab-3674-4e7d-beed-a6eca3835856

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSmallerUnitaryGroupEmbedding
import Theorems.Thm_GlobalTheory_SatakeWeyl_InclusionMultiplication_incl_mul_apply
import Theorems.Thm_GlobalTheory_SatakeWeyl_InclusionMultiplication_incl_mul_apply_of_not
import Theorems.Thm_GlobalTheory_SatakeWeyl_InclusionMultiplication_mul_inclT_apply
import Theorems.Thm_GlobalTheory_SatakeWeyl_InclusionMultiplication_mul_inclT_apply_of_not
import Theorems.Thm_GlobalTheory_SatakeWeyl_InclusionMultiplication_extendMatrixByIdentityAlongIndices_mul
import Theorems.Thm_GlobalTheory_SatakeWeyl_InclusionMultiplication_extendMatrixByIdentityAlongIndices_unitary
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
import Theorems.Thm_GlobalTheory_SatakeWeyl_exists_mat
import Theorems.Thm_GlobalTheory_SatakeWeyl_mat_injective
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
open GlobalTheory.SatakeWeyl.InclusionMultiplication
namespace GlobalTheory.SatakeWeyl
theorem _root_.solution : GlobalTheory.SatakeWeyl.EmbExists := by
  intro L _ _ σ n r e he hr
  choose f hf using fun g : GU σ r => exists_mat (σ := σ) (ext1 e (mat g)) (extendMatrixByIdentityAlongIndices_unitary σ he hr _ g.2)
  refine ⟨MonoidHom.mk' f fun a b => mat_injective ?_, fun g => ⟨fun i j => ?_, fun a b hab => ?_⟩⟩
  · rw [mat_mul, hf, hf, hf, mat_mul, extendMatrixByIdentityAlongIndices_mul he]
  · rw [MonoidHom.mk'_apply, hf, ext1, Matrix.add_apply, mul_inclT_apply he, incl_mul_apply he]
    simp [Matrix.one_apply, he.eq_iff]
  · rw [MonoidHom.mk'_apply, hf, ext1, Matrix.add_apply]
    rcases hab with h | h
    · rw [Matrix.mul_assoc, incl_mul_apply_of_not _ h, add_zero]
    · rw [mul_inclT_apply_of_not _ _ h, add_zero]
end GlobalTheory.SatakeWeyl
