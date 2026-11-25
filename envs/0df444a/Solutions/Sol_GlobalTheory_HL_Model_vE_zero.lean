-- Prove2me | solution 1 for GlobalTheory.HL.Model.vE_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:45:44.660712+00:00
-- url     : https://prove2.me/submissions/3c547169-8f74-4f46-bf2d-33f52758c2b3

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
theorem _root_.solution (L : LocE F E) (ϖ : 𝒪[F]) : vE L ϖ 0 = 0 := by
  unfold vE
  have hS : {m : ℤ | ∃ y ∈ L.O, (0 : E) = algebraMap F E ((ϖ : F) ^ m) * y} = Set.univ :=
    Set.eq_univ_of_forall fun m => ⟨0, L.O.zero_mem, by simp⟩
  rw [hS]
  rw [csSup_of_not_bddAbove not_bddAbove_univ]
  exact Int.csSup_empty
end GlobalTheory.HL.Model
