-- Prove2me | solution 1 for GroundTheory.Automorphic.enorm_sq_eq_tsum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:05:21.050952+00:00
-- url     : https://prove2.me/submissions/b0cbe19d-e770-4c83-afc6-2cca549f8b01

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HilbertSchmidt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open scoped ENNReal InnerProductSpace InnerProduct
open ContinuousLinearMap
noncomputable section
variable {𝕜 : Type*} [RCLike 𝕜]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]
  {L : Type*} [NormedAddCommGroup L] [InnerProductSpace 𝕜 L] [CompleteSpace L]
namespace GroundTheory.Automorphic
theorem _root_.solution {ι : Type*} (b : HilbertBasis ι 𝕜 H) (x : H) :
    ‖x‖ₑ ^ 2 = ∑' i, ‖⟪b i, x⟫_𝕜‖ₑ ^ 2 := by
  have hp : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  have h1 := lp.norm_rpow_eq_tsum hp (b.repr x)
  have h2 := (lp.memℓp (b.repr x)).summable hp
  simp only [LinearIsometryEquiv.norm_map, HilbertBasis.repr_apply_apply, ENNReal.toReal_ofNat,
    Real.rpow_two] at h1 h2
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), h1,
    ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity) h2]
  congr 1
  ext i
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
end GroundTheory.Automorphic
