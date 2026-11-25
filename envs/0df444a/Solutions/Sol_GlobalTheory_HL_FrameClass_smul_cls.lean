-- Prove2me | solution 1 for GlobalTheory.HL.FrameClass.smul_cls
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:33:55.551674+00:00
-- url     : https://prove2.me/submissions/5d7b0c44-67b8-49ac-8e71-a554699c809b

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetFrameClassProperties
import Theorems.Thm_GlobalTheory_HL_FrameClass_smul_mem
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.FrameClass
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
namespace GlobalTheory.HL.FrameClass
theorem _root_.solution (h : S.GLV) (g g' : Fin (r + 1) → S.V) :
    h • S.frameCls g g' = S.frameCls (fun b => h (g b)) (fun b => h (g' b)) := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact smul_mem S h hq
  · intro hp
    have := smul_mem S h⁻¹ hp
    refine ⟨h⁻¹ • p, ?_, smul_inv_smul h p⟩
    have e : ∀ v : S.V, h⁻¹ (h v) = v := fun v => h.symm_apply_apply v
    simpa only [e] using this
end GlobalTheory.HL.FrameClass
