-- Prove2me | solution 1 for GlobalTheory.UnRep.Compare.isUnE_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:57:06.460221+00:00
-- url     : https://prove2.me/submissions/bbb29b60-6b46-4389-a445-7988884b2045

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AdelicCMFields_SupportedAtSplit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLatticeRationalVectorsInAdelicTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsSplitPlaceOfSplitPl
import Theorems.Thm_GlobalTheory_UnRep_Compare_isUnA_iff
import Theorems.Thm_GlobalTheory_UnRep_Compare_fm_eq_ratM
import Theorems.Thm_GlobalTheory_UnRep_Compare_inc_injective
import Theorems.Thm_GlobalTheory_UnRep_Compare_unitary_iff_matrix
import Theorems.Thm_GlobalTheory_UnRep_Compare_isUnA_iff_matrix
import Theorems.Thm_GlobalTheory_UnRep_Compare_fm_eq_map
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnRep GlobalTheory.UnRep.Compare
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceUnitaryEvaluation
open scoped TensorProduct Matrix
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
namespace GlobalTheory.UnRep.Compare
theorem _root_.solution (c : E ≃ₐ[F] E) {n : ℕ} (G γ : Matrix (Fin n) (Fin n) E) :
    IsUnE c G γ ↔ IsUnitaryA c G (ratM F γ) := by
  have h1 : IsUnE c G γ ↔ γᵀ * G * γ.map (c : E →+* E) = G := unitary_iff_matrix (c : E →+* E) G γ
  have h2 : (fm F γ).map (sg (FiniteAdeleRing (𝓞 F) F) c).toRingHom = fm F (γ.map (c : E →+* E)) := by
    ext a b
    simp [fm, sg]
  rw [← isUnA_iff, ← fm_eq_ratM, isUnA_iff_matrix, h1, h2, fm_eq_map, fm_eq_map, fm_eq_map,
    ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul]
  exact (Matrix.map_injective inc_injective).eq_iff.symm
end GlobalTheory.UnRep.Compare
