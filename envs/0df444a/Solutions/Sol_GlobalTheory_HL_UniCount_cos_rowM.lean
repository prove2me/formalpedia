-- Prove2me | solution 1 for GlobalTheory.HL.UniCount.cos_rowM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:13:54.412134+00:00
-- url     : https://prove2.me/submissions/4ad23e14-3e85-470a-8fef-a0c618749484

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardQuotEqPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EncardUniCosetsLe
import Theorems.Thm_GlobalTheory_HL_UniCount_mul_rowM
import Theorems.Thm_GlobalTheory_HL_UniCount_isUni_rowM
import Theorems.Thm_GlobalTheory_HL_UniCount_isIntM_rowM
import Theorems.Thm_GlobalTheory_HL_UniCount_cos_mul_subset
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
theorem _root_.solution (L : LocE F E) (u : Matrix (Fin N) (Fin N) E) (k : Fin N) (c : Fin N → E)
    (hc : ∀ j, j ≤ k → c j = 0) (hc' : ∀ j, c j ∈ L.O) : cos L (u * rowM k c) = cos L u := by
  refine (cos_mul_subset L u _ (isUni_rowM k c hc) (isIntM_rowM L k c hc')).antisymm ?_
  have : u = u * rowM k c * rowM k (-c) := by
    ext i j
    rw [mul_rowM, mul_rowM, mul_rowM, hc k le_rfl]
    simp
  conv_lhs => rw [this]
  exact cos_mul_subset L _ _ (isUni_rowM k _ fun j hj => by simp [hc j hj])
    (isIntM_rowM L k _ fun j => neg_mem (hc' j))
end GlobalTheory.HL.UniCount
