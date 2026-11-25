-- Prove2me | solution 1 for GlobalTheory.OrbitDenom.block_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:34:53.189806+00:00
-- url     : https://prove2.me/submissions/69115658-94aa-4177-b1cb-91fef8cf33dd

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEqZpowMulUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeadingMinorsProdDenominatorUnitriangularFactors
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
open GlobalTheory GlobalTheory.OrbitDenom
variable {E : Type} [CommRing E]
namespace GlobalTheory.OrbitDenom
theorem _root_.solution : ∀ (bs : List (Eˣ × ℕ+)) (i : ℕ), i < (bs.map (fun b => (b.2 : ℕ))).sum →
    ∃ (l' l : ℕ) (t : E), l' ≤ i ∧ i < l ∧ l ≤ (bs.map (fun b => (b.2 : ℕ))).sum ∧
      (∀ a b, l' ≤ a → a < l → l' ≤ b → b < l → sameBlock bs a b = true) ∧
      (∀ a b, l' ≤ a → a < l → ptEntryL bs a b = if a + b + 1 = l + l' then t else 0) ∧
      (∀ a b, l ≤ a → b < l → ptEntryL bs a b = 0) ∧ (∀ a b, l' ≤ a → b < l' → ptEntryL bs a b = 0)
  | [], i, h => by simp at h
  | (t, s) :: bs, i, h => by
    simp only [List.map_cons, List.sum_cons] at h ⊢
    by_cases h1 : i < s
    · refine ⟨0, s, t, by omega, h1, by omega, ?_, ?_, ?_, ?_⟩
      · intro a b _ ha _ hb
        simp [sameBlock, ha, hb]
      · intro a b _ ha
        simp only [ptEntryL]
        split_ifs <;> first | rfl | omega
      · intro a b ha hb
        simp only [ptEntryL]
        split_ifs <;> first | rfl | omega
      · intro a b ha hb
        omega
    · obtain ⟨l', l, t', e1, e2, e3, e4, e5, e6, e7⟩ := solution bs (i - s) (by omega)
      refine ⟨s + l', s + l, t', by omega, by omega, by omega, ?_, ?_, ?_, ?_⟩
      · intro a b ha' ha hb' hb
        have := e4 (a - s) (b - s) (by omega) (by omega) (by omega) (by omega)
        simp only [sameBlock, this, Bool.and_true, Bool.or_eq_true, decide_eq_true_eq]
        omega
      · intro a b ha' ha
        simp only [ptEntryL, e5 (a - s) (b - s) (by omega) (by omega)]
        split_ifs <;> first | rfl | omega
      · intro a b ha hb
        simp only [ptEntryL]
        split_ifs
        · omega
        · omega
        · exact e6 _ _ (by omega) (by omega)
        · rfl
      · intro a b ha hb
        simp only [ptEntryL]
        split_ifs
        · omega
        · omega
        · exact e7 _ _ (by omega) (by omega)
        · rfl
end GlobalTheory.OrbitDenom
