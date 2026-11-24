-- Prove2me | solution 1 for GlobalTheory.SmoothForms.DerLinear.der_eq_fderiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:51:56.323909+00:00
-- url     : https://prove2.me/submissions/bda72f17-b844-43ac-acd6-6933b474ac7b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_RightDerivativeAlongLieSmoothAndLinear

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology
open GlobalTheory GlobalTheory.SmoothForms GlobalTheory.SmoothForms.DerLinear
variable {𝔸 L G : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸] [NormedAddCommGroup L]
  [NormedSpace ℝ L] [Group G] {σ : 𝔸 →ₗ[ℝ] 𝔸} {j : L →ₗ[ℝ] 𝔸} {s : 𝔸 → G}
omit [FiniteDimensional ℝ 𝔸]
namespace GlobalTheory.SmoothForms.DerLinear
theorem _root_.solution {e : L → G} {φ : G → ℂ} (hφ : Sm e φ) (X : L) (g : G) :
    Der e X φ g = fderiv ℝ (fun Z : L => φ (g * e Z)) 0 X := by
  have hF : DifferentiableAt ℝ (fun Z : L => φ (g * e Z)) 0 :=
    ((contDiff_infty_iff_fderiv.1 (hφ g)).1) 0
  have hd : HasDerivAt (fun t : ℝ => t • X) X 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const X
  have hF' : HasFDerivAt (fun Z : L => φ (g * e Z)) (fderiv ℝ (fun Z : L => φ (g * e Z)) 0) ((0 : ℝ) • X) := by
    rw [zero_smul]
    exact hF.hasFDerivAt
  exact (hF'.comp_hasDerivAt (0 : ℝ) hd).deriv
end GlobalTheory.SmoothForms.DerLinear
