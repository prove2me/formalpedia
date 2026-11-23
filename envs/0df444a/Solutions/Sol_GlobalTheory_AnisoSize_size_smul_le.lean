-- Prove2me | solution 1 for GlobalTheory.AnisoSize.size_smul_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:22:46.487525+00:00
-- url     : https://prove2.me/submissions/7fc5d5ff-d7dd-4399-a65f-d9313cd5671d

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
theorem _root_.solution (H : Sized h Λ N ν B) {U : ℝ} (hU : 2 ≤ U) {a b : ℕ} {c : E} {x : V}
    (hc : house c ≤ U ^ a) (hx : ν x ≤ U ^ b) : ν (c • x) ≤ U ^ (a + b) :=
  (H.smul_le c x).trans (mul_le_pow hU hc hx (H.nonneg x))
end GlobalTheory.AnisoSize
