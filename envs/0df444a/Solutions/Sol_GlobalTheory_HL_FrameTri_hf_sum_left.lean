-- Prove2me | solution 1 for GlobalTheory.HL.FrameTri.hf_sum_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:57:18.733574+00:00
-- url     : https://prove2.me/submissions/6492d29d-3ca8-4305-889b-50467e948d22

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FrameUnipotentUnitriangular
import Theorems.Thm_GlobalTheory_HL_FrameTri_hf_add_left
import Theorems.Thm_GlobalTheory_HL_FrameTri_hf_smul_left
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.FrameTri
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.HL.FrameTri
theorem _root_.solution (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) {ι : Type} (s : Finset ι)
    (c : ι → E) (g : ι → Fin n → E) (y : Fin n → E) :
    hf L Hm (∑ i ∈ s, c i • g i) y = ∑ i ∈ s, c i * hf L Hm (g i) y := by
  induction s using Finset.induction_on with
  | empty => simp [hf]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hf_add_left, hf_smul_left, ih]
end GlobalTheory.HL.FrameTri
