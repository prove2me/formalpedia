-- Prove2me | solution 1 for GlobalTheory.KeyKa.kosBlock_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:08:34.058566+00:00
-- url     : https://prove2.me/submissions/0f124f38-ecad-4ac1-8bbb-020506ed4ce2

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
theorem _root_.solution :
    (kosBlock (fun _ => 1) 1 : Matrix (KIx g d N) (KIx g d N) R) = 1 := by
  have : (Matrix.blockDiagonal' fun I : Finset (Fin g) =>
      (1 : Matrix (Fin (N I.card)) (Fin (N I.card)) R)) = 1 := Matrix.blockDiagonal'_one
  rw [kosBlock, this, Matrix.fromBlocks_one]
end GlobalTheory.KeyKa
