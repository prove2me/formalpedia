-- Prove2me | solution 1 for GlobalTheory.KeyKa.kosBlock_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:31:11.623773+00:00
-- url     : https://prove2.me/submissions/3906dedd-47a9-4ed4-98be-c0d28cb3a225

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
theorem _root_.solution (C C' : ∀ j, Matrix (Fin (N j)) (Fin (N j)) R) (P P' : Matrix (Fin d) (Fin d) R) :
    (kosBlock C P : Matrix (KIx g d N) (KIx g d N) R) * kosBlock C' P' =
      kosBlock (fun j => C j * C' j) (P * P') := by
  simp [kosBlock, Matrix.fromBlocks_multiply, ← Matrix.blockDiagonal'_mul]
end GlobalTheory.KeyKa
