-- Prove2me | solution 1 for GlobalTheory.AnisoSize.size_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:59:07.191807+00:00
-- url     : https://prove2.me/submissions/d4e54e60-c023-4817-93d4-9a8dfdaa2438

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
theorem _root_.solution (H : Sized h Λ N ν B) {ι : Type} (s : Finset ι) (x : ι → V) :
    ν (∑ i ∈ s, x i) ≤ ∑ i ∈ s, ν (x i) := by
  refine Finset.le_sum_of_subadditive ν ?_ H.add_le s x
  have h1 := H.smul_le 0 0
  have h2 := house_intCast (K := E) 0
  simp only [Int.cast_zero, abs_zero] at h2
  rwa [h2, zero_smul, zero_mul] at h1
end GlobalTheory.AnisoSize
