-- Prove2me | solution 1 for GlobalTheory.CoeffWord.wordOf_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:14:33.361632+00:00
-- url     : https://prove2.me/submissions/74dbbede-d169-4046-8670-8cec41de8320

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_UnitriMonomialOfLowerTri
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open GlobalTheory GlobalTheory.CoeffWord
variable {R : Type} [CommRing R] {r n : ℕ}
namespace GlobalTheory.CoeffWord
theorem _root_.solution (e : Fin r × Fin n →₀ ℕ) : wordOf e = (positions r n).map (letter e) := by
  rw [wordOf, positions, List.map_flatMap]
  congr 1
  funext s
  rw [List.map_map]
  generalize List.finRange r = l
  induction l with
  | nil => simp
  | cons a l ih =>
    by_cases h : s.val < a.val
    · have hr : s.val < r := lt_trans h a.2
      rw [List.filterMap_cons, dif_pos ⟨h, hr⟩, List.filter_cons_of_pos (by simpa using h)]
      simp only [List.map_cons, ih]
      simp [letter, hr]
    · rw [List.filterMap_cons, dif_neg (fun h' => h h'.1), List.filter_cons_of_neg (by simpa using h)]
      exact ih
end GlobalTheory.CoeffWord
