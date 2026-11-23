-- Prove2me | solution 1 for GlobalTheory.KeyKa.kosBlock_graded
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:08:33.980809+00:00
-- url     : https://prove2.me/submissions/9e4d1151-9dae-43c7-ac5f-0b8808370700

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_DegProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SubmatrixMulOfSupport
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_KosBlockMulKosD

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.KeyKa
open GlobalTheory GlobalTheory.KeyKa
variable {R : Type} [CommRing R] {g d : ℕ} {N : ℕ → ℕ}
namespace GlobalTheory.KeyKa
theorem _root_.solution (C : ∀ j, Matrix (Fin (N j)) (Fin (N j)) R) (P : Matrix (Fin d) (Fin d) R)
    (p q : KIx g d N) (h : kdeg p ≠ kdeg q) : kosBlock C P p q = 0 := by
  rcases p with ⟨I, a⟩ | a <;> rcases q with ⟨J, b⟩ | b
  · have : I ≠ J := by rintro rfl; exact h rfl
    simp [kosBlock, Matrix.blockDiagonal'_apply_ne _ _ _ this]
  · simp [kosBlock]
  · simp [kosBlock]
  · exact absurd rfl h
end GlobalTheory.KeyKa
