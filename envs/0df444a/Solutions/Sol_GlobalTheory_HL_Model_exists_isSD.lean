-- Prove2me | solution 1 for GlobalTheory.HL.Model.exists_isSD
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:51:34.647797+00:00
-- url     : https://prove2.me/submissions/a97e97c4-2f43-4f16-bc3d-d65e677af342

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_HermitianLattices
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIntegralIff
import Theorems.Thm_GlobalTheory_HL_Model_isHermND_one
import Theorems.Thm_GlobalTheory_HL_Model_isSD_std
import Theorems.Thm_GlobalTheory_HL_Model_nonempty_split
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_SelfDualHermitianLatticesTorsionBlocks_isHermND_one


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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.Model
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.HL.Model
theorem _root_.solution [IsNonarchimedeanLocalField F] (n : ℕ) :
    ∃ (L : LocE F (F × F)) (H : Matrix (Fin n) (Fin n) (F × F)) (Λ : Submodule L.O (Fin n → F × F)),
      IsHermND L H ∧ IsSD L H Λ := by
  obtain ⟨L, -, -⟩ := nonempty_split (F := F)
  exact ⟨L, 1, stdLat L n, isHermND_one L n, isSD_std L n⟩
end GlobalTheory.HL.Model
