-- Prove2me | solution 1 for GlobalTheory.SmoothForms.DerLinear.sm_der
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:18:21.991697+00:00
-- url     : https://prove2.me/submissions/7875dedd-a101-4c3a-803a-6ce4dd899bee

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_RightDerivativeAlongLieSmoothAndLinear
import Theorems.Thm_GlobalTheory_SmoothForms_DerLinear_exp_unitary
import Theorems.Thm_GlobalTheory_SmoothForms_DerLinear_contDiff_exp
import Theorems.Thm_GlobalTheory_SmoothForms_contDiff_family


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
namespace GlobalTheory.SmoothForms.DerLinear
theorem _root_.solution (H : IsLieData σ j s) (hl : HasLog σ j) {φ : G → ℂ} (hφ : Sm (expMap j s) φ) (X : L) :
    Sm (expMap j s) (Der (expMap j s) X φ) := by
  intro g
  have hu1 : ∀ Z : L, σ (NormedSpace.exp (j Z)) * NormedSpace.exp (j Z) = 1 := exp_unitary H
  let c : L × ℝ → 𝔸 := fun p => NormedSpace.exp (j p.1) * NormedSpace.exp (j (p.2 • X))
  have hcd : ContDiff ℝ ∞ c :=
    ((contDiff_exp H).comp contDiff_fst).mul ((contDiff_exp H).comp (contDiff_snd.smul contDiff_const))
  have hcu : ∀ p, σ (c p) * c p = 1 := by
    intro p
    simp only [c]
    rw [H.anti, mul_assoc, ← mul_assoc (σ (NormedSpace.exp (j p.1))), hu1, one_mul, hu1]
  have hφ0 : ∀ g, ContDiffAt ℝ ∞ (fun X : L => φ (g * expMap j s X)) 0 := fun g => (hφ g).contDiffAt
  have hF := contDiff_family H hl hφ0 hcd hcu g
  have key : ∀ Y : L, Der (expMap j s) X φ (g * expMap j s Y) =
      fderiv ℝ (fun p : L × ℝ => φ (g * s (c p))) (Y, 0) ((0 : L), (1 : ℝ)) := by
    intro Y
    have h1 : (fun t : ℝ => φ (g * expMap j s Y * expMap j s (t • X))) = fun t => φ (g * s (c (Y, t))) := by
      funext t
      simp only [c, expMap, mul_assoc, H.mul _ _ (hu1 Y) (hu1 (t • X))]
    have hd : HasDerivAt (fun t : ℝ => ((Y, t) : L × ℝ)) ((0 : L), (1 : ℝ)) 0 :=
      (hasDerivAt_const (0 : ℝ) Y).prodMk (hasDerivAt_id 0)
    have hFd : HasFDerivAt (fun p : L × ℝ => φ (g * s (c p)))
        (fderiv ℝ (fun p : L × ℝ => φ (g * s (c p))) (Y, 0)) (Y, 0) :=
      ((contDiff_infty_iff_fderiv.1 hF).1 _).hasFDerivAt
    show deriv (fun t : ℝ => φ (g * expMap j s Y * expMap j s (t • X))) 0 = _
    rw [h1]
    exact (hFd.comp_hasDerivAt (0 : ℝ) hd).deriv
  simp_rw [key]
  exact (((contDiff_infty_iff_fderiv.1 hF).2).comp (contDiff_id.prodMk contDiff_const)).clm_apply contDiff_const
end GlobalTheory.SmoothForms.DerLinear
