-- Prove2me | solution 1 for GlobalTheory.QNorm.val_integer_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:44:21.663995+00:00
-- url     : https://prove2.me/submissions/95c9bdf1-c85f-4ef8-a412-ccaa39c0d394

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsQuadraticSqrtExtensionBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsTwoPlacesOverOfIsSquareLocal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
open GlobalTheory GlobalTheory.QNorm
namespace GlobalTheory.QNorm
theorem _root_.solution {E Γ : Type} [Field E] [LinearOrderedCommGroupWithZero Γ]
    (u : Valuation E Γ) (x : 𝓞 E) : u (algebraMap (𝓞 E) E x) ≤ 1 := by
  have h : IsIntegral u.integer (algebraMap (𝓞 E) E x) :=
    (RingOfIntegers.isIntegral_coe x).tower_top
  exact (Valuation.integer.integers u).mem_of_integral h
end GlobalTheory.QNorm
