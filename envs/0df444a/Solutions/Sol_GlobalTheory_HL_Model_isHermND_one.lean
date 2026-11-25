-- Prove2me | solution 1 for GlobalTheory.HL.Model.isHermND_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:40:30.939146+00:00
-- url     : https://prove2.me/submissions/a6cfcba5-db64-49b3-a81a-b0f970ebcb48

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
theorem _root_.solution (L : LocE F E) (n : ℕ) : IsHermND L (1 : Matrix (Fin n) (Fin n) E) := by
  refine ⟨?_, by simp⟩
  ext i j
  show L.cj ((1 : Matrix (Fin n) (Fin n) E) j i) = (1 : Matrix (Fin n) (Fin n) E) i j
  by_cases hij : i = j
  · subst hij
    simp
  · simp [hij, Ne.symm hij]
end GlobalTheory.HL.Model
