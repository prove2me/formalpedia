-- Prove2me | solution 1 for GlobalTheory.KeyKa.kosBlock_mul_inr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:31:15.308749+00:00
-- url     : https://prove2.me/submissions/fa7547e3-ec86-481d-8f6f-450a0d039ec6

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
    (D : Matrix (KIx g d N) (KIx g d N) R) (a : Fin d) (q : KIx g d N) :
    (kosBlock C P * D : Matrix (KIx g d N) (KIx g d N) R) (.inr a) q = ∑ c, P a c * D (.inr c) q := by
  rw [Matrix.mul_apply, Fintype.sum_sum_type]
  simp [kosBlock]
end GlobalTheory.KeyKa
