-- Prove2me | solution 1 for GlobalTheory.KeyKa.kosBlock_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:31:09.341794+00:00
-- url     : https://prove2.me/submissions/105c246b-ca65-4c1f-8417-c10c84147750

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
theorem _root_.solution (C C' : ∀ j, Matrix (Fin (N j)) (Fin (N j)) R)
    (P P' : Matrix (Fin d) (Fin d) R) (p q : KIx g d N)
    (h1 : ∀ j, kdeg p = j + 1 → C j = C' j) (h2 : kdeg p = 0 → P = P') :
    kosBlock C P p q = kosBlock C' P' p q := by
  rcases p with ⟨I, a⟩ | a <;> rcases q with ⟨J, b⟩ | b
  · simp only [kosBlock, Matrix.fromBlocks_apply₁₁, Matrix.blockDiagonal'_apply]
    rw [h1 I.card rfl]
  · simp [kosBlock]
  · simp [kosBlock]
  · rw [h2 rfl]; simp [kosBlock]
end GlobalTheory.KeyKa
