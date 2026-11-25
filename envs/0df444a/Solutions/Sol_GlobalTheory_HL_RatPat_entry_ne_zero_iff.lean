-- Prove2me | solution 1 for GlobalTheory.HL.RatPat.entry_ne_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:32:47.457781+00:00
-- url     : https://prove2.me/submissions/99f7b2fe-d155-4bd0-a474-60ebd7fa63fa

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
theorem _root_.solution {R : Type} [CommRing R] [Nontrivial R] (bs : List (Rˣ × ℕ+)) (a b : ℕ)
    (ha : a < (bs.map (fun b => (b.2 : ℕ))).sum) :
    ptEntryL bs a b ≠ 0 ↔ b = rhoL bs a := by
  induction bs generalizing a b with
  | nil => simp at ha
  | cons c bs ih =>
    obtain ⟨t, s⟩ := c
    rw [sum_cons'] at ha
    simp only [ptEntryL, rhoL]
    by_cases h1 : a < (s : ℕ)
    · rw [if_pos h1]
      by_cases h2 : b < (s : ℕ)
      · rw [if_pos ⟨h1, h2⟩]
        split_ifs with h3
        · simp only [ne_eq, Units.ne_zero, not_false_eq_true, true_iff]; omega
        · simp only [ne_eq, not_true_eq_false, false_iff]; omega
      · rw [if_neg (fun h => h2 h.2), if_neg (fun h => by omega)]
        simp only [ne_eq, not_true_eq_false, false_iff]; omega
    · rw [if_neg h1, if_neg (fun h => h1 h.1)]
      by_cases h2 : (s : ℕ) ≤ b
      · rw [if_pos ⟨by omega, h2⟩, ih (a - s) (b - s) (by omega)]
        omega
      · rw [if_neg (fun h => h2 h.2)]
        simp only [ne_eq, not_true_eq_false, false_iff]; omega
end GlobalTheory.HL.RatPat
