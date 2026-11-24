-- Prove2me | solution 1 for GlobalTheory.AnisoSize.house_sub_le_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:14:33.387034+00:00
-- url     : https://prove2.me/submissions/f9bc6f32-eb16-433e-9413-12238e95fc2f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__ExistsIntMulIsIntegralOfTrace_d66162b46f1d0309
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsNeZeroMemFractionalIdealNormSqLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_AnisotropicFiniteLengthsOfShortLatticeVector
import Theorems.Thm_GlobalTheory_AnisoSize_house_neg
import Theorems.Thm_GlobalTheory_AnisoSize_add_le_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SmoothForms NumberField Matrix Module Submodule
open scoped ContDiff Topology nonZeroDivisors
open GlobalTheory GlobalTheory.AnisoSize
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {V : Type} [AddCommGroup V] [Module E V]
  {h : V →ₗ[E] V →ₗ⋆[E] E} {Λ : Submodule ℤ V} {N : ℤ} {ν : V → ℝ} {B : ℝ}
omit [IsCMField E]
namespace GlobalTheory.AnisoSize
theorem _root_.solution {U : ℝ} (hU : 2 ≤ U) {a b : ℕ} {x y : E}
    (hx : house x ≤ U ^ a) (hy : house y ≤ U ^ b) : house (x - y) ≤ U ^ (max a b + 1) := by
  rw [sub_eq_add_neg]
  exact (house_add_le _ _).trans (add_le_pow hU hx (by rwa [house_neg]))
end GlobalTheory.AnisoSize
