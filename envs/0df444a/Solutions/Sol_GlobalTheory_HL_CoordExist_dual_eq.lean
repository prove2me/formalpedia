-- Prove2me | solution 1 for GlobalTheory.HL.CoordExist.dual_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:06:31.654317+00:00
-- url     : https://prove2.me/submissions/ecfc5773-5b9f-4d43-9ee7-83cb8edadbfb

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GgNone
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NotField
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
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.CoordExist
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]
namespace GlobalTheory.HL.CoordExist
theorem _root_.solution {H : HermSp M V} {r : ℕ} (A : LocNG.FrameD H r) (a : Fin (r + 1)) (j : Fin r) :
    H.h (A.f a) (A.es j) = if a = j.castSucc then 1 else 0 := by
  induction a using Fin.lastCases with
  | last =>
    rw [if_neg (Fin.castSucc_lt_last j).ne', H.h_herm, A.h_sz, map_zero]
  | cast i =>
    rw [A.h_es i j]
    simp only [Fin.castSucc_inj]
end GlobalTheory.HL.CoordExist
