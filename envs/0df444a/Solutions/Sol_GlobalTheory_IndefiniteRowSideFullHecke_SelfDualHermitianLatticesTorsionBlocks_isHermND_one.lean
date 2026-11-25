-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.SelfDualHermitianLatticesTorsionBlocks.isHermND_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T06:17:26.756679+00:00
-- url     : https://prove2.me/submissions/f57709e1-4eaf-480a-ad7f-e008095d3f02

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_HermitianLattices
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
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.SelfDualHermitianLatticesTorsionBlocks
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.IndefiniteRowSideFullHecke.SelfDualHermitianLatticesTorsionBlocks
theorem _root_.solution (L : LocE F E) (n : ℕ) :
    IsHermND L (1 : Matrix (Fin n) (Fin n) E) := by
  refine ⟨fun i j => ?_, by simp⟩
  by_cases h : i = j
  · subst h; simp
  · simp [Matrix.one_apply_ne h, Matrix.one_apply_ne (Ne.symm h)]
end GlobalTheory.IndefiniteRowSideFullHecke.SelfDualHermitianLatticesTorsionBlocks
