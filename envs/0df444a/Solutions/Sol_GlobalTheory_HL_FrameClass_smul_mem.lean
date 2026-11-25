-- Prove2me | solution 1 for GlobalTheory.HL.FrameClass.smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T06:09:41.132917+00:00
-- url     : https://prove2.me/submissions/1a89816d-9e76-49fb-8371-a0314619af4b

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetFrameClassProperties
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
theorem _root_.solution (h : S.GLV) {g g' : Fin (r + 1) → S.V} {p : S.FrP} (hp : p ∈ S.frameCls g g') :
    h • p ∈ S.frameCls (fun b => h (g b)) (fun b => h (g' b)) := by
  obtain ⟨A, A', hA, hA', ht, hd, hc, h1, h2⟩ := hp
  refine ⟨A, A', hA, hA', ht, hd, hc, fun j => ?_, fun j => ?_⟩
  · show h (p.1 j) = _
    rw [h1]; simp
  · show h (p.2 j) = _
    rw [h2]; simp
end GlobalTheory.HL.FrameClass
