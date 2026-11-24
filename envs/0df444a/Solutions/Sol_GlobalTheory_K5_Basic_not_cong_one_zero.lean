-- Prove2me | solution 1 for GlobalTheory.K5.Basic.not_cong_one_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:39:59.188798+00:00
-- url     : https://prove2.me/submissions/3d984c35-ad70-4542-b7d6-aa0f8414baae

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_NotCoboundaryConstantOne
import Theorems.Thm_GlobalTheory_K5_Basic_not_isUnit_p

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.K5 GlobalTheory.K5.Basic
open Polynomial
variable {p : ℕ} [hp : Fact p.Prime] {Ω : Type*} [Field Ω] [Algebra (O0 p) Ω]
namespace GlobalTheory.K5.Basic
theorem _root_.solution (h : IsClo p Ω) (k : ℕ) (hk : k ≠ 0) : ¬ Cong p k (1 : Ω) 0 := by
  rintro ⟨z, hz, h1⟩
  haveI : FaithfulSMul (O0 p) (integralClosure (O0 p) Ω) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 fun a b hab => h.inj (congrArg Subtype.val hab)
  have hu : IsUnit (algebraMap (O0 p) (integralClosure (O0 p) Ω) (p ^ k)) :=
    IsUnit.of_mul_eq_one ⟨z, hz⟩ (Subtype.ext (by simpa using h1.symm))
  haveI : IsLocalHom (algebraMap (O0 p) (integralClosure (O0 p) Ω)) :=
    Algebra.IsIntegral.isLocalHom _ _
  exact not_isUnit_p p ((isUnit_pow_iff hk).1 (isUnit_of_map_unit _ _ hu))
end GlobalTheory.K5.Basic
