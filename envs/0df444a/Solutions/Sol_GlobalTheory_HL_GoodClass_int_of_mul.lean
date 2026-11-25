-- Prove2me | solution 1 for GlobalTheory.HL.GoodClass.int_of_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:36:49.818235+00:00
-- url     : https://prove2.me/submissions/242ae56d-9de8-405e-9630-296f76610ec1

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
theorem _root_.solution (O : Subring E) (M U : Matrix (Fin n) (Fin n) E) (hU : UpU U)
    (hM : ∀ m, ∃ i, UnitIn O (M i m) ∧ ∀ m', m < m' → M i m' = 0)
    (hZ : ∀ i j, (M * U) i j ∈ O) (m : Fin n) : (∀ i, M i m ∈ O) ∧ ∀ j, U m j ∈ O := by
  induction m using WellFoundedLT.induction with
  | ind m ih =>
  have key : ∀ i j, (∀ c, m < c → M i c * U c j = 0) → M i m * U m j ∈ O := by
    intro i j h
    have h1 := hZ i j
    rw [Matrix.mul_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ m)] at h1
    have h2 : ∑ c ∈ Finset.univ.erase m, M i c * U c j ∈ O := by
      refine O.sum_mem fun c hc => ?_
      rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hc) with h3 | h3
      · exact O.mul_mem ((ih c h3).1 i) ((ih c h3).2 j)
      · rw [h c h3]; exact O.zero_mem
    simpa using O.sub_mem h1 h2
  refine ⟨fun i => ?_, fun j => ?_⟩
  · have := key i m fun c hc => by rw [hU.1 c m hc, mul_zero]
    rwa [hU.2, mul_one] at this
  · obtain ⟨i, ⟨_, y, hy, hy1⟩, h0⟩ := hM m
    have := O.mul_mem hy (key i j fun c hc => by rw [h0 c hc, zero_mul])
    rwa [← mul_assoc, mul_comm y, hy1, one_mul] at this
end GlobalTheory.HL.GoodClass
