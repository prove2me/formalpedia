-- Prove2me | solution 1 for GlobalTheory.AnisoSize.abs_norm_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:00:20.519496+00:00
-- url     : https://prove2.me/submissions/3724cbba-4afb-429f-82c4-880596fecd5e

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
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.AnisoSize
theorem _root_.solution (a : E) : ((|Algebra.norm ℚ a| : ℚ) : ℝ) = ∏ φ : E →+* ℂ, ‖φ a‖ := by
  have h := Algebra.norm_eq_prod_embeddings ℚ ℂ a
  rw [← Fintype.prod_equiv (RingHom.equivRatAlgHom E ℂ) (fun φ : E →+* ℂ => φ a) _ (fun _ => rfl)] at h
  rw [← norm_prod, ← h]
  simp
end GlobalTheory.AnisoSize
