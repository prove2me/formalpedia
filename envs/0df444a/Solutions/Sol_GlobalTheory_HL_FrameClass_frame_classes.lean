-- Prove2me | solution 1 for GlobalTheory.HL.FrameClass.frame_classes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:18:06.950804+00:00
-- url     : https://prove2.me/submissions/bac16772-c40f-4a6c-b770-63da0bee4e26

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetFrameClassProperties
import Theorems.Thm_GlobalTheory_HL_FrameClass_refl_mem
import Theorems.Thm_GlobalTheory_HL_FrameClass_trans_mem
import Theorems.Thm_GlobalTheory_HL_FrameClass_symm_mem
import Theorems.Thm_GlobalTheory_HL_FrameClass_Mof_le
import Theorems.Thm_GlobalTheory_HL_FrameClass_smul_cls

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.FrameClass
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
namespace GlobalTheory.HL.FrameClass
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ g g' : Fin (r + 1) → S.V, (g, g') ∈ S.frameCls g g' ∧ (∀ p ∈ S.frameCls g g', S.frameCls p.1 p.2 = S.frameCls g g' ∧ S.Mof p.1 p.2 = S.Mof g g') ∧ ∀ h : S.GLV, h • S.frameCls g g' = S.frameCls (fun b => h (g b)) (fun b => h (g' b)) := by
  intro F _ _ _ _ _ E _ _ _ L r k S g g'
  refine ⟨refl_mem S g g', fun p hp => ⟨?_, ?_⟩, fun h => smul_cls S h g g'⟩
  · ext q
    exact ⟨fun hq => trans_mem S hp hq, fun hq => trans_mem S (symm_mem S hp) hq⟩
  · exact le_antisymm (Mof_le S hp) (Mof_le S (p := (g, g')) (symm_mem S hp))
end GlobalTheory.HL.FrameClass
