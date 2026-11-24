-- Prove2me | solution 1 for GlobalTheory.CoeffWord.mem_positions
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:12:22.829233+00:00
-- url     : https://prove2.me/submissions/88fdb39f-a68a-45de-b1b2-665207e9e9b2

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
theorem _root_.solution (v : Fin r × Fin n) : v ∈ positions r n ↔ v.2.val < v.1.val := by
  obtain ⟨a, s⟩ := v
  simp [positions]
end GlobalTheory.CoeffWord
