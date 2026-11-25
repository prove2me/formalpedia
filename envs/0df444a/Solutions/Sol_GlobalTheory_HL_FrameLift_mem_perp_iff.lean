-- Prove2me | solution 1 for GlobalTheory.HL.FrameLift.mem_perp_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:36:47.28689+00:00
-- url     : https://prove2.me/submissions/326cecdf-1d6b-4c4b-9146-6e453a365b2f

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DualInterSelfDualHermitianLatticeSubspace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SelfDualLatticeUnipotentTranslateStandard
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HL_Eichler_hf_cj
import Theorems.Thm_GlobalTheory_HL_FrameOnto_hf_spanTo
import Theorems.Thm_GlobalTheory_HL_FrameOnto_mem_spanTo
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.FrameLift
open GlobalTheory.HL.Eichler GlobalTheory.HL.FrameOnto
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
namespace GlobalTheory.HL.FrameLift
theorem _root_.solution (g : Fin (r + 1) → S.V) (v : S.V) :
    v ∈ perp L S.Hm (S.spanTo g r) ↔ ∀ j : Fin r, hf L S.Hm v (g j.castSucc) = 0 := by
  refine ⟨fun h j => h _ (mem_spanTo S g (by simp)), fun h y hy => ?_⟩
  rw [← hf_cj L S.herm.1, hf_spanTo S g hy, map_zero]
  intro i hi
  have := h ⟨i, hi⟩
  rw [← hf_cj L S.herm.1]
  have e : (Fin.castSucc (⟨i, hi⟩ : Fin r)) = i := Fin.ext rfl
  rw [e] at this
  rw [this, map_zero]
end GlobalTheory.HL.FrameLift
