-- Prove2me | solution 1 for GlobalTheory.HL.ContModel.isPrimT_std
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:45:39.976843+00:00
-- url     : https://prove2.me/submissions/337d50fd-fa38-415e-9ae6-1cc757763040

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NcardImageOfLe
import Theorems.Thm_GlobalTheory_HL_ContModel_hf_single

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.ContModel
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.HL.ContModel
theorem _root_.solution (L : LocE F E) {n : ℕ} (Λ : Submodule L.O (Fin n → E))
    (h : ∀ a, (Pi.single a 1 : Fin n → E) ∈ Λ) : IsPrimT L 1 Λ (fun a => Pi.single a 1) :=
  ⟨h, _, h, fun a b => by rw [hf_single, Matrix.one_apply]⟩
end GlobalTheory.HL.ContModel
