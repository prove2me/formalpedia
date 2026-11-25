-- Prove2me | solution 1 for GlobalTheory.HL.RatPat.rhoL_rhoL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:32:58.879157+00:00
-- url     : https://prove2.me/submissions/a2158102-0e3b-44ef-b9e8-0d5e3f2344a3

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianStabiliserRationalUnitriangularPairsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RationalExtend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BlockUnitriangularRationalFromCommonStabiliser
import Theorems.Thm_P2M_GlobalTheory_HL_RatPat_sum_cons__0b43592650e5
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
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.RatPat
namespace GlobalTheory.HL.RatPat
theorem _root_.solution {R : Type} [CommRing R] (bs : List (Rˣ × ℕ+)) (a : ℕ)
    (ha : a < (bs.map (fun b => (b.2 : ℕ))).sum) : rhoL bs (rhoL bs a) = a := by
  induction bs generalizing a with
  | nil => rfl
  | cons b bs ih =>
    obtain ⟨t, s⟩ := b
    rw [sum_cons'] at ha
    by_cases h : a < (s : ℕ)
    · have e : rhoL ((t, s) :: bs) a = (s : ℕ) - 1 - a := by simp [rhoL, h]
      rw [e]; simp only [rhoL]; rw [if_pos (by omega)]; omega
    · have e : rhoL ((t, s) :: bs) a = (s : ℕ) + rhoL bs (a - s) := by simp [rhoL, h]
      rw [e]; simp only [rhoL]
      rw [if_neg (by omega), Nat.add_sub_cancel_left, ih (a - s) (by omega)]; omega
end GlobalTheory.HL.RatPat
