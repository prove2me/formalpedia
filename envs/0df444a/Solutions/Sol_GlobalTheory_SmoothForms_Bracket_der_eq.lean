-- Prove2me | solution 1 for GlobalTheory.SmoothForms.Bracket.der_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:42:34.371117+00:00
-- url     : https://prove2.me/submissions/ff4b231e-b235-4e1a-9691-a9918e80b324

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_RightDerivativeAlongLieCommutatorEqBracket
import Theorems.Thm_GlobalTheory_SmoothForms_Bracket_exp_unitary
import Theorems.Thm_GlobalTheory_SmoothForms_Bracket_unitary_mul
import Theorems.Thm_GlobalTheory_SmoothForms_Bracket_hasDerivAt_exp

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
open GlobalTheory GlobalTheory.SmoothForms GlobalTheory.SmoothForms.Bracket
variable {𝔸 L G : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸] [NormedAddCommGroup L]
  [NormedSpace ℝ L] [Group G] {σ : 𝔸 →ₗ[ℝ] 𝔸} {j : L →ₗ[ℝ] 𝔸} {s : 𝔸 → G}
namespace GlobalTheory.SmoothForms.Bracket
theorem _root_.solution (H : IsLieData σ j s) {φ : G → ℂ} {g : G} {F : 𝔸 → ℂ} {a : 𝔸} (ha : σ a * a = 1)
    (hF : DifferentiableAt ℝ F a) (he : ∀ᶠ h in 𝓝 a, σ h * h = 1 → φ (g * s h) = F h) (Y : L) :
    Der (expMap j s) Y φ (g * s a) = fderiv ℝ F a (a * j Y) := by
  have : CompleteSpace 𝔸 := FiniteDimensional.complete ℝ 𝔸
  have hcd : HasDerivAt (fun t : ℝ => a * NormedSpace.exp (t • j Y)) (a * j Y) 0 :=
    (hasDerivAt_exp (j Y)).const_mul a
  have hc0 : a * NormedSpace.exp ((0 : ℝ) • j Y) = a := by
    rw [zero_smul, NormedSpace.exp_zero, mul_one]
  have hu : ∀ t : ℝ, σ (NormedSpace.exp (t • j Y)) * NormedSpace.exp (t • j Y) = 1 := fun t => by
    simpa [map_smul] using exp_unitary H (t • Y)
  have hFd : HasFDerivAt F (fderiv ℝ F a) (a * NormedSpace.exp ((0 : ℝ) • j Y)) := by
    rw [hc0]; exact hF.hasFDerivAt
  have hFc := hFd.comp_hasDerivAt (x := (0 : ℝ)) hcd
  have hlim : Filter.Tendsto (fun t : ℝ => a * NormedSpace.exp (t • j Y)) (𝓝 0) (𝓝 a) := by
    have := hcd.continuousAt.tendsto
    rwa [hc0] at this
  have heq : (fun t : ℝ => φ (g * s a * expMap j s (t • Y))) =ᶠ[𝓝 0]
      (fun t : ℝ => F (a * NormedSpace.exp (t • j Y))) := by
    filter_upwards [hlim.eventually he] with t ht
    have hm : g * s a * s (NormedSpace.exp (j (t • Y))) = g * s (a * NormedSpace.exp (t • j Y)) := by
      rw [j.map_smul t Y, mul_assoc, ← H.mul a _ ha (hu t)]
    show φ (g * s a * s (NormedSpace.exp (j (t • Y)))) = _
    rw [hm]
    exact ht (unitary_mul H ha (hu t))
  show deriv (fun t : ℝ => φ (g * s a * expMap j s (t • Y))) 0 = _
  exact (hFc.congr_of_eventuallyEq heq).deriv
end GlobalTheory.SmoothForms.Bracket
