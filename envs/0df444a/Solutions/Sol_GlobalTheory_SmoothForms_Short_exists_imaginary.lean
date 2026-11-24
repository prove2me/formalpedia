-- Prove2me | solution 1 for GlobalTheory.SmoothForms.Short.exists_imaginary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:52:00.492794+00:00
-- url     : https://prove2.me/submissions/c95f46be-f25b-4976-bbde-1aa844fa492a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__ExistsIntMulIsIntegralOfTrace_d66162b46f1d0309
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ShortLatticeVectorBoundedSizeOfOrthogonalFrame
import Theorems.Thm_GlobalTheory_HermClass_exists_int_mul_isIntegral
import Theorems.Thm_GlobalTheory_HermClass_isIntegral_star


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SmoothForms GlobalTheory.HermClass Module Submodule NumberField Matrix
open GlobalTheory GlobalTheory.SmoothForms GlobalTheory.SmoothForms.Short
namespace GlobalTheory.SmoothForms.Short
theorem _root_.solution (E : Type) [Field E] [NumberField E] [IsCMField E] :
    ∃ δ : E, δ ≠ 0 ∧ IsIntegral ℤ δ ∧ star δ = -δ := by
  obtain ⟨x, hx⟩ : ∃ x : E, star x ≠ x := by
    by_contra hc
    push Not at hc
    exact IsCMField.complexConj_ne_one E (AlgEquiv.ext hc)
  obtain ⟨M, hM, hMa⟩ := exists_int_mul_isIntegral E (Set.finite_singleton x)
  have hi := hMa x rfl
  refine ⟨M * x - star (M * x), ?_, hi.sub (isIntegral_star hi), by simp⟩
  rw [star_mul', star_intCast, ← mul_sub]
  exact mul_ne_zero (by exact_mod_cast hM) (sub_ne_zero.2 hx.symm)
end GlobalTheory.SmoothForms.Short
