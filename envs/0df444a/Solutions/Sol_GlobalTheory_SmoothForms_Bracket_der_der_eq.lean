-- Prove2me | solution 1 for GlobalTheory.SmoothForms.Bracket.der_der_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:51:54.652791+00:00
-- url     : https://prove2.me/submissions/1954b74c-1492-4bd9-8199-3ce85c7d35a5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_RightDerivativeAlongLieCommutatorEqBracket
import Theorems.Thm_GlobalTheory_SmoothForms_Bracket_exp_unitary
import Theorems.Thm_GlobalTheory_SmoothForms_Bracket_hasDerivAt_exp
import Theorems.Thm_GlobalTheory_SmoothForms_Bracket_der_eq

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
theorem _root_.solution (H : IsLieData σ j s) {φ : G → ℂ} {g : G} {F : 𝔸 → ℂ}
    (hF : ContDiffAt ℝ 2 F 1) (he : ∀ᶠ h in 𝓝 (1 : 𝔸), σ h * h = 1 → φ (g * s h) = F h) (X Y : L) :
    Der (expMap j s) X (Der (expMap j s) Y φ) g =
      fderiv ℝ (fderiv ℝ F) 1 (j X) (j Y) + fderiv ℝ F 1 (j X * j Y) := by
  have : CompleteSpace 𝔸 := FiniteDimensional.complete ℝ 𝔸
  have hcd : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • j X)) (j X) 0 := hasDerivAt_exp (j X)
  have hc0 : NormedSpace.exp ((0 : ℝ) • j X) = 1 := by rw [zero_smul, NormedSpace.exp_zero]
  have hlim : Filter.Tendsto (fun t : ℝ => NormedSpace.exp (t • j X)) (𝓝 0) (𝓝 1) := by
    have := hcd.continuousAt.tendsto
    rwa [hc0] at this
  have hu : ∀ t : ℝ, σ (NormedSpace.exp (t • j X)) * NormedSpace.exp (t • j X) = 1 := fun t => by
    simpa [map_smul] using exp_unitary H (t • X)
  have hF1 : ContDiffAt ℝ 1 (fderiv ℝ F) 1 := hF.fderiv_right (by norm_num)
  have hA : HasFDerivAt (fderiv ℝ F) (fderiv ℝ (fderiv ℝ F) 1) (NormedSpace.exp ((0 : ℝ) • j X)) := by
    rw [hc0]; exact (hF1.differentiableAt one_ne_zero).hasFDerivAt
  have h1 : HasDerivAt (fun t : ℝ => fderiv ℝ F (NormedSpace.exp (t • j X)))
      (fderiv ℝ (fderiv ℝ F) 1 (j X)) 0 := hA.comp_hasDerivAt (x := (0 : ℝ)) hcd
  have h3 := h1.clm_apply (hcd.mul_const (j Y))
  have hd : ∀ᶠ y in 𝓝 (1 : 𝔸), DifferentiableAt ℝ F y :=
    (hF.eventually (by simp)).mono fun y hy => hy.differentiableAt two_ne_zero
  have hev : ∀ᶠ y in 𝓝 (1 : 𝔸), DifferentiableAt ℝ F y ∧
      ∀ᶠ h in 𝓝 y, σ h * h = 1 → φ (g * s h) = F h := hd.and he.eventually_nhds
  have heq : (fun t : ℝ => Der (expMap j s) Y φ (g * expMap j s (t • X))) =ᶠ[𝓝 0]
      (fun t : ℝ => fderiv ℝ F (NormedSpace.exp (t • j X)) (NormedSpace.exp (t • j X) * j Y)) := by
    filter_upwards [hlim.eventually hev] with t ht
    show Der (expMap j s) Y φ (g * s (NormedSpace.exp (j (t • X)))) = _
    rw [j.map_smul t X]
    exact der_eq H (hu t) ht.1 ht.2 Y
  show deriv (fun t : ℝ => Der (expMap j s) Y φ (g * expMap j s (t • X))) 0 = _
  rw [(h3.congr_of_eventuallyEq heq).deriv, hc0, one_mul]
end GlobalTheory.SmoothForms.Bracket
