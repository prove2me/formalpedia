-- Prove2me | solution 1 for GlobalTheory.HL.Model.not_isLat_bot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:45:29.469357+00:00
-- url     : https://prove2.me/submissions/178042ec-cb7b-4aac-a146-c84c55470161

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_HermitianLattices
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIntegralIff
import Theorems.Thm_GlobalTheory_HL_Model_nontrivial
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.Model
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.HL.Model
theorem _root_.solution (L : LocE F E) (n : ℕ) : ¬ IsLat L (⊥ : Submodule L.O (Fin (n + 1) → E)) := by
  rintro ⟨-, h⟩
  have := nontrivial L
  simp at h
end GlobalTheory.HL.Model
