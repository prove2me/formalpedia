-- Prove2me | solution 1 for GlobalTheory.QNorm.norm_of_isSquare_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:40:43.625905+00:00
-- url     : https://prove2.me/submissions/a2ee59bb-f8f0-4302-a66e-a2ec55f43e10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_TwoPowCardLeIndexIInfStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsApproxModLocalSquaresStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsLocalNonnormOfNonsquareAdicCompletionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IndexUnitsLocalSquaresFiniteRealPlacesLeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_TwoPowLeIndexLocalNormsSqrtExtension

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
theorem _root_.solution {L : Type} [Field L] {x y δ : L} (hx : x ≠ 0)
    (h : IsSquare (x * y)) (hn : ∃ a b : L, x = a ^ 2 - δ * b ^ 2) :
    ∃ a b : L, y = a ^ 2 - δ * b ^ 2 := by
  obtain ⟨s, hs⟩ := h
  obtain ⟨a, b, hab⟩ := hn
  refine ⟨a * s / x, b * s / x, ?_⟩
  field_simp
  linear_combination x * hs + s ^ 2 * hab
end GlobalTheory.QNorm
