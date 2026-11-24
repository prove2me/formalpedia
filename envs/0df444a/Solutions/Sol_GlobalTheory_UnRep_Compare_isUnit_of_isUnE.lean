-- Prove2me | solution 1 for GlobalTheory.UnRep.Compare.isUnit_of_isUnE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:45:01.216803+00:00
-- url     : https://prove2.me/submissions/3ece18cb-64c1-47ad-878f-106d2f385a57

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AdelicCMFields_SupportedAtSplit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLatticeRationalVectorsInAdelicTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsSplitPlaceOfSplitPl
import Theorems.Thm_GlobalTheory_UnRep_Compare_unitary_iff_matrix

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
omit [NumberField F]
namespace GlobalTheory.UnRep.Compare
theorem _root_.solution (c : E ≃ₐ[F] E) {n : ℕ} {G : Matrix (Fin n) (Fin n) E} (hG : G.det ≠ 0)
    {γ : Matrix (Fin n) (Fin n) E} (hγ : IsUnE c G γ) : IsUnit γ := by
  have h := congrArg Matrix.det ((unitary_iff_matrix (c : E →+* E) G γ).1 hγ)
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, mul_assoc] at h
  rw [Matrix.isUnit_iff_isUnit_det]
  exact isUnit_of_mul_isUnit_left (h.symm ▸ IsUnit.mk0 _ hG)
end GlobalTheory.UnRep.Compare
