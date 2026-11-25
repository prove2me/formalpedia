-- Prove2me | solution 1 for GlobalTheory.HL.ContModel.smul_inf_of_fix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:43:45.12831+00:00
-- url     : https://prove2.me/submissions/1a03c863-a523-42e2-8071-16140ec1ecbf

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NcardImageOfLe
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.ContModel
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.HL.ContModel
theorem _root_.solution (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
    (Y : Submodule E (Fin n → E)) (g : fixG L Hm Y) (Λ : Submodule L.O (Fin n → E)) :
    (g • Λ) ⊓ Y.restrictScalars L.O = Λ ⊓ Y.restrictScalars L.O := by
  obtain ⟨g, hg⟩ := g
  obtain ⟨_, h1, h2⟩ := hg
  have h3 : ∀ v ∈ Y, g v = v := fun v hv => sub_eq_zero.1 (by simpa using h2 v hv)
  ext v
  simp only [Submodule.mem_inf, Submodule.restrictScalars_mem]
  constructor
  · rintro ⟨⟨w, hw, rfl⟩, hv⟩
    have hw' : w ∈ Y := (h1 w).1 hv
    refine ⟨?_, hv⟩
    change g w ∈ Λ
    rw [h3 w hw']; exact hw
  · rintro ⟨hv, hY⟩
    exact ⟨⟨v, hv, h3 v hY⟩, hY⟩
end GlobalTheory.HL.ContModel
