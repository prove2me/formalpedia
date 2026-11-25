-- Prove2me | solution 1 for GlobalTheory.FrameLevel.exists_coords
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:15:19.43114+00:00
-- url     : https://prove2.me/submissions/765caca7-c986-4782-87d2-31cdd9810c43

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetFramesLevelLeIffCongrFlagSte
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
open GlobalTheory GlobalTheory.FrameLevel
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.FrameLevel
theorem _root_.solution {L : LocE F E} {r k : ℕ} (S : Frames L r k) (g : Fin (r + 1) → S.V) (j : ℕ)
    {y : S.V} (hy : y ∈ S.spanTo g j) :
    ∃ a : Fin (r + 1) → E, y = ∑ i, a i • g i ∧ ∀ i : Fin (r + 1), j ≤ (i : ℕ) → a i = 0 := by
  obtain ⟨c, hc, rfl⟩ := (Finsupp.mem_span_image_iff_linearCombination E).mp hy
  refine ⟨c, ?_, fun i hi => ?_⟩
  · rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)]
  · by_contra hne
    have hmem : i ∈ {i : Fin (r + 1) | (i : ℕ) < j} :=
      (Finsupp.mem_supported _ _).mp hc (Finsupp.mem_support_iff.mpr hne)
    exact absurd hi (not_le.mpr hmem)
end GlobalTheory.FrameLevel
