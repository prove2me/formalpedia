-- Prove2me | solution 1 for GlobalTheory.HermClass.exists_int_mul_isIntegral
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:11:34.649794+00:00
-- url     : https://prove2.me/submissions/42b6239c-056b-4856-8e11-9eda7b0e4ef1

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__ExistsShortOfTraceDet_f72bcdc76e7ca34f
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__ExistsIntMulIsIntegralOfTrace_d66162b46f1d0309

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.HermClass
open Module Submodule NumberField
variable (E : Type) [Field E] [NumberField E]
namespace GlobalTheory.HermClass
theorem _root_.solution {S : Set E} (hS : S.Finite) :
    ∃ M : ℤ, M ≠ 0 ∧ ∀ a ∈ S, IsIntegral ℤ ((M : E) * a) := by
  obtain ⟨M, hM, h⟩ := exists_integral_multiples ℤ ℚ hS.toFinset
  exact ⟨M, hM, fun a ha => by simpa using h a (by simpa using ha)⟩
end GlobalTheory.HermClass
