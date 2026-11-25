-- Prove2me | solution 1 for GlobalTheory.HL.Model.unipOn_top_bot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:45:40.369339+00:00
-- url     : https://prove2.me/submissions/b216b7b3-5057-444b-a479-aafaf66483bd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_HermitianLattices
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIntegralIff
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
theorem _root_.solution {n : ℕ} : unipOn (E := E) (n := n) ⊤ ⊥ = ⊥ := by
  refine eq_bot_iff.mpr fun g hg => (Subgroup.mem_bot).mpr ?_
  refine LinearEquiv.ext fun v => ?_
  have h2 := hg.2 v Submodule.mem_top
  rw [Submodule.mem_bot, sub_eq_zero] at h2
  simpa using h2
end GlobalTheory.HL.Model
