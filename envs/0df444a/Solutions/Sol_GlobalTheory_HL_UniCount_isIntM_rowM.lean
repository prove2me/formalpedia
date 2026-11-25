-- Prove2me | solution 1 for GlobalTheory.HL.UniCount.isIntM_rowM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:40:27.403807+00:00
-- url     : https://prove2.me/submissions/80b3d49c-2029-40d3-a6f6-adf7f41b7993

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardQuotEqPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EncardUniCosetsLe
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
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.UniCount
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] {N : ℕ}
namespace GlobalTheory.HL.UniCount
theorem _root_.solution (L : LocE F E) (k : Fin N) (c : Fin N → E) (hc : ∀ j, c j ∈ L.O) :
    IsIntM L (rowM k c) := fun i j => by
  simp only [rowM, Matrix.add_apply, Matrix.of_apply, Matrix.one_apply]
  refine add_mem ?_ ?_
  · split_ifs
    exacts [one_mem _, zero_mem _]
  · split_ifs
    exacts [hc j, zero_mem _]
end GlobalTheory.HL.UniCount
