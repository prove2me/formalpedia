-- Prove2me | solution 1 for GlobalTheory.SepPoint.exists_clear_poly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:44:36.481408+00:00
-- url     : https://prove2.me/submissions/d4b0f91a-45da-405a-8a23-2c21c8f9efbb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsIntegrallyClosedAdjoin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPrimitiveElementSeparabilityCertificate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open scoped IntermediateField.algebraAdjoinAdjoin
open GlobalTheory GlobalTheory.SepPoint
namespace GlobalTheory.SepPoint
theorem _root_.solution {k F : Type} [Field k] [Field F] [Algebra k F] (s : Set F)
    (p : (IntermediateField.adjoin k s)[X]) :
    ∃ q : (Algebra.adjoin k s)[X], ∃ b : Algebra.adjoin k s, b ≠ 0 ∧
      q.map (algebraMap (Algebra.adjoin k s) (IntermediateField.adjoin k s)) =
        C (algebraMap (Algebra.adjoin k s) (IntermediateField.adjoin k s) b) * p := by
  obtain ⟨b, hb, h⟩ :=
    IsLocalization.integerNormalization_spec (nonZeroDivisors (Algebra.adjoin k s)) p
  refine ⟨IsLocalization.integerNormalization (nonZeroDivisors (Algebra.adjoin k s)) p, b,
    nonZeroDivisors.ne_zero hb, ?_⟩
  rw [h, ← IsScalarTower.algebraMap_smul (IntermediateField.adjoin k s) b p, Polynomial.smul_eq_C_mul]
end GlobalTheory.SepPoint
