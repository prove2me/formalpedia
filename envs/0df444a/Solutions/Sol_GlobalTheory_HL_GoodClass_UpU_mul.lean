-- Prove2me | solution 1 for GlobalTheory.HL.GoodClass.UpU.mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T06:12:59.331156+00:00
-- url     : https://prove2.me/submissions/6eae6bb1-5712-45f7-a17e-f80fad0ed33e

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FramesCommonStabiliserEqPairingMatrixStabiliser
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetFrameClassProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_UnitEntries
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
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.GoodClass
variable {E : Type} [CommRing E] {n : ℕ}
namespace GlobalTheory.HL.GoodClass
namespace UpU
theorem _root_.solution {s t : Matrix (Fin n) (Fin n) E} (hs : UpU s) (ht : UpU t) : UpU (s * t) := by
  refine ⟨fun i j h => ?_, fun i => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    rcases lt_or_ge c i with h1 | h1
    · rw [hs.1 i c h1, zero_mul]
    · rw [ht.1 c j (lt_of_lt_of_le h h1), mul_zero]
  · rw [Matrix.mul_apply, Finset.sum_eq_single i, hs.2, ht.2, one_mul]
    · intro c _ hc
      rcases lt_or_gt_of_ne hc with h1 | h1
      · rw [hs.1 i c h1, zero_mul]
      · rw [ht.1 c i h1, mul_zero]
    · simp
end UpU
end GlobalTheory.HL.GoodClass
