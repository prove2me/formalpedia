-- Prove2me | solution 1 for GlobalTheory.HL.FrameTri.sub_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:58:44.486264+00:00
-- url     : https://prove2.me/submissions/ff7e6669-b8e6-4c9b-accf-218244b3c208

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FrameUnipotentUnitriangular
import Theorems.Thm_GlobalTheory_HL_FrameTri_mem_spanTo
import Theorems.Thm_GlobalTheory_HL_FrameTri_last_mem_perp
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
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
variable (g : Fin (r + 1) → S.V) (gs : Fin r → S.V) (t : Fˣ)
  (hg : ∀ a b, hf L S.Hm (g a) (g b) =
    if a = Fin.last r ∧ b = Fin.last r then -algebraMap F E t else 0)
  (hd : ∀ a j, hf L S.Hm (g a) (gs j) = if a = j.castSucc then 1 else 0)
include hg
namespace GlobalTheory.HL.FrameTri
theorem _root_.solution {n : S.GLV} (hn : n ∈ S.Nof g) (i : Fin (r + 1)) :
    n (g i) - g i ∈ S.spanTo g i := by
  obtain ⟨⟨_, h2⟩, h3⟩ := hn
  refine Fin.lastCases ?_ (fun j => ?_) i
  · exact h3.2 _ (last_mem_perp S g t hg)
  · have h := (Subgroup.mem_iInf.1 h2 j).2 (g j.castSucc) (mem_spanTo S g (by simp))
    exact h
end GlobalTheory.HL.FrameTri
