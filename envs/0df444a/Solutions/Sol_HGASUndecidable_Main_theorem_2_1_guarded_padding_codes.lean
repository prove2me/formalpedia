-- Prove2me | solution 1 for HGASUndecidable.Main.theorem_2_1_guarded_padding_codes
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:29:30.42392+00:00
-- url     : https://prove2.me/submissions/925bddf6-3b8d-4d98-b673-88e722e8795e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_HGASUndecidable_Main_validCode_computablePred
import Theorems.Thm_HGASUndecidable_Main_paddingCode_computable
import Theorems.Thm_HGASUndecidable_Main_guardedPaddingMap_computable
import Theorems.Thm_HGASUndecidable_Main_paddingCode_spec

open Filter Topology MeasureTheory
open scoped BigOperators
open HGASUndecidable.Main

theorem solution (n₀ k₀ n j : ℕ)
    (hn₀ : 1 ≤ n₀) (hk₀ : 1 ≤ k₀) (hn : Nat.choose (n₀+k₀-1) k₀ ≤ n)
    (f : ℕ → ℕ) (hf : Computable f) :
    ∃ r : ℕ → ℕ, Computable r ∧
      (∀ e c (terms : List (ℕ × List ℕ × ℚ)),
        decodeField e = some c → ValidCode c → c.1 = n₀ →
        c.2.1 = 2*k₀+1 →
        decodeField (f (Encodable.encode c)) =
          some (Nat.choose (n₀+k₀-1) k₀, 3, terms) →
        ValidCode (Nat.choose (n₀+k₀-1) k₀, 3, terms) →
        ∃ outTerms : List (ℕ × List ℕ × ℚ),
          decodeField (r e) = some (n, 3+2*j, outTerms) ∧
          ValidCode (n, 3+2*j, outTerms) ∧
          codeField (n, 3+2*j, outTerms) = padding hn j
            (codeField (Nat.choose (n₀+k₀-1) k₀, 3, terms))) ∧
      (∀ e q, decodeField (r e) = some q → ValidCode q →
        ∃ c, decodeField e = some c ∧ ValidCode c ∧ c.1 = n₀ ∧
          c.2.1 = 2*k₀+1) := by
  obtain ⟨inst, hv⟩ := validCode_computablePred
  letI : DecidablePred ValidCode := inst
  let r := guardedPaddingMap n₀ k₀ n j hn f
  refine ⟨r, guardedPaddingMap_computable n₀ k₀ n j hn f validCode_computablePred
    (paddingCode_computable hn j) hf, ?_, ?_⟩
  · intro e c terms he hcv hcn hcd hlift hliftv
    have hr : r e = paddingCode hn j terms := by
      simp [r, guardedPaddingMap, he, hcv, hcn, hcd, hlift, hliftv]
    obtain ⟨outTerms, hdecode, hvalid, hfield⟩ := paddingCode_spec hn j terms hliftv
    exact ⟨outTerms, hr ▸ hdecode, hvalid, hfield⟩
  · intro e q hrq hqv
    by_cases hs : ∃ c, decodeField e = some c ∧ ValidCode c ∧ c.1 = n₀ ∧
        c.2.1 = 2*k₀+1
    · exact hs
    · exfalso
      have hr : r e = Encodable.encode ((0, 1, []) : RawFieldCode) := by
        simp only [r, guardedPaddingMap]
        cases he : decodeField e with
        | none => simp
        | some c =>
            have hc : ¬(ValidCode c ∧ c.1 = n₀ ∧ c.2.1 = 2*k₀+1) := by
              intro hc
              apply hs
              exact ⟨c, he, hc.1, hc.2.1, hc.2.2⟩
            simp [hc]
      rw [hr] at hrq
      have hbad : decodeField (Encodable.encode ((0, 1, []) : RawFieldCode)) =
          some ((0, 1, []) : RawFieldCode) := Encodable.encodek _
      have hq : ((0, 1, []) : RawFieldCode) = q := Option.some.inj (hbad.symm.trans hrq)
      rw [← hq] at hqv
      exact Nat.not_succ_le_zero 0 hqv.1
