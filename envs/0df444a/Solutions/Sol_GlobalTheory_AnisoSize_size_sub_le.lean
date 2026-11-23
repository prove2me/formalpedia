-- Prove2me | solution 1 for GlobalTheory.AnisoSize.size_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:22:46.616941+00:00
-- url     : https://prove2.me/submissions/44fce2dd-e1e8-4716-a926-99b793658bd5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__ExistsIntMulIsIntegralOfTrace_d66162b46f1d0309
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsNeZeroMemFractionalIdealNormSqLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_AnisotropicFiniteLengthsOfShortLatticeVector

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
theorem _root_.solution (H : Sized h Λ N ν B) (x y : V) : ν (x - y) ≤ ν x + ν y := by
  have h1 := H.smul_le (-1) y
  have h2 := house_intCast (K := E) (-1)
  simp only [Int.reduceNeg, Int.cast_neg, Int.cast_one, abs_neg, abs_one] at h2
  rw [h2, neg_smul, one_smul, one_mul] at h1
  rw [sub_eq_add_neg]
  linarith [H.add_le x (-y)]
end GlobalTheory.AnisoSize
