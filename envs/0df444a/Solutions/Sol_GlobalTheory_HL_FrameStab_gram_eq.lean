-- Prove2me | solution 1 for GlobalTheory.HL.FrameStab.gram_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:06:50.839817+00:00
-- url     : https://prove2.me/submissions/ad75989a-1d14-4a5d-970e-7c3b12d0ef27

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FramesCommonStabiliserEqPairingMatrixStabiliser
import Theorems.Thm_GlobalTheory_HL_FrameStab_hf_sum
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.FrameStab
open GlobalTheory.HL.Eichler GlobalTheory.HL.FrameOnto
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
namespace GlobalTheory.HL.FrameStab
theorem _root_.solution (g : Fin (r + 1) → S.V) (T : Fˣ)
    (gram : ∀ a b, hf L S.Hm (g a) (g b) =
      if a = Fin.last r ∧ b = Fin.last r then -algebraMap F E T else 0)
    (s : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (hs : (∀ i j, j < i → s i j = 0) ∧ (∀ i, s i i = 1))
    (a b : Fin (r + 1)) :
    hf L S.Hm (∑ i, s i a • g i) (∑ i, s i b • g i) = hf L S.Hm (g a) (g b) := by
  have hl : ∀ a, s (Fin.last r) a = if a = Fin.last r then 1 else 0 := by
    intro a
    split_ifs with h
    · rw [h, hs.2]
    · exact hs.1 _ _ (lt_of_le_of_ne (Fin.le_last a) h)
  rw [hf_sum, Finset.sum_eq_single (Fin.last r), Finset.sum_eq_single (Fin.last r)]
  · rw [hl, hl, gram, gram]
    by_cases ha : a = Fin.last r <;> by_cases hb : b = Fin.last r <;> simp [ha, hb]
  · intro j _ hj; simp [gram, hj]
  · simp
  · intro j _ hj; simp [gram, hj]
  · simp
end GlobalTheory.HL.FrameStab
