-- Prove2me | solution 1 for GlobalTheory.AnisoSize.house_form_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:22:45.767176+00:00
-- url     : https://prove2.me/submissions/dc0ed4ba-c693-4f0a-88d9-2ce2321376d0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__ExistsIntMulIsIntegralOfTrace_d66162b46f1d0309
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsNeZeroMemFractionalIdealNormSqLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_AnisotropicFiniteLengthsOfShortLatticeVector
import Theorems.Thm_GlobalTheory_AnisoSize_mul_le_pow

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
namespace GlobalTheory.AnisoSize
theorem _root_.solution (H : Sized h Λ N ν B) {U : ℝ} (hU : 2 ≤ U) {a b : ℕ} {x y : V}
    (hx : ν x ≤ U ^ a) (hy : ν y ≤ U ^ b) : house (h x y) ≤ U ^ (a + b) :=
  (H.form_le x y).trans (mul_le_pow hU hx hy (H.nonneg y))
end GlobalTheory.AnisoSize
