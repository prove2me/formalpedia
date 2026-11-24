-- Prove2me | solution 1 for GlobalTheory.UnRep.Compare.isUnit_of_isUnA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:02:27.672864+00:00
-- url     : https://prove2.me/submissions/83a6b02b-d9d9-479c-8701-a56008ce28d7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AdelicCMFields_SupportedAtSplit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLatticeRationalVectorsInAdelicTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsSplitPlaceOfSplitPl
import Theorems.Thm_GlobalTheory_UnRep_Compare_isUnA_iff_matrix
import Theorems.Thm_GlobalTheory_UnRep_Compare_fm_eq_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnRep GlobalTheory.UnRep.Compare
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceUnitaryEvaluation
open scoped TensorProduct Matrix
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
namespace GlobalTheory.UnRep.Compare
theorem _root_.solution (c : E ≃ₐ[F] E) {n : ℕ} {G : Matrix (Fin n) (Fin n) E} (hG : G.det ≠ 0)
    {g : Matrix (Fin n) (Fin n) (RA F E)} (hg : IsUnA c G g) : IsUnit g := by
  have h := congrArg Matrix.det ((isUnA_iff_matrix c G g).1 hg)
  have hu : IsUnit (fm F G).det := by
    rw [fm_eq_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (IsUnit.mk0 _ hG).map _
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, mul_assoc] at h
  rw [Matrix.isUnit_iff_isUnit_det]
  exact isUnit_of_mul_isUnit_left (h.symm ▸ hu)
end GlobalTheory.UnRep.Compare
