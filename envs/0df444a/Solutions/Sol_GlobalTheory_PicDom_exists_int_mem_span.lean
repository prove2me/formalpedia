-- Prove2me | solution 1 for GlobalTheory.PicDom.exists_int_mem_span
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:02:48.828992+00:00
-- url     : https://prove2.me/submissions/e6756d7b-0e45-44c5-9a74-b29abd151ec5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOfFinOrderOfIsOfFinOrderMapRingHomStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PicIsOfFinOrderOfFiniteInt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open NumberField
open GlobalTheory GlobalTheory.PicDom
namespace GlobalTheory.PicDom
theorem _root_.solution {B : Type} [CommRing B] [IsDomain B] [Algebra.IsIntegral ℤ B] {d : B} (hd : d ≠ 0) :
    ∃ a : ℤ, a ≠ 0 ∧ (a : B) ∈ Ideal.span {d} := by
  have h := Ideal.comap_ne_bot_of_integral_mem hd (Ideal.mem_span_singleton_self d)
    (Algebra.IsIntegral.isIntegral (R := ℤ) d)
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  exact ⟨a, ha0, by simpa using ha⟩
end GlobalTheory.PicDom
