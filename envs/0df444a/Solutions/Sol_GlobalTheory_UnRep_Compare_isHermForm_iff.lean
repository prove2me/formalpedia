-- Prove2me | solution 1 for GlobalTheory.UnRep.Compare.isHermForm_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:44:59.266363+00:00
-- url     : https://prove2.me/submissions/b23c835d-99a2-47ee-9b49-7f699e2d6e9b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AdelicCMFields_SupportedAtSplit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLatticeRationalVectorsInAdelicTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsSplitPlaceOfSplitPl
import Theorems.Thm_GlobalTheory_UnRep_Compare_conj_conj

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
theorem _root_.solution (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) {n : ℕ} (G : Matrix (Fin n) (Fin n) E) :
    IsHermForm c G ↔ c ≠ 1 ∧ (∀ a b, G b a = c (G a b)) ∧ G.det ≠ 0 :=
  ⟨fun h => ⟨h.2.1, fun a b => (h.2.2.1 a b).symm, h.2.2.2⟩,
    fun h => ⟨conj_conj c h2 h.1, h.1, fun a b => (h.2.1 a b).symm, h.2.2⟩⟩
end GlobalTheory.UnRep.Compare
