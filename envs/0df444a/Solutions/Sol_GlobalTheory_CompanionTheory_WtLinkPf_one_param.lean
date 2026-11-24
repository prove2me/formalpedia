-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.WtLinkPf.one_param
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:01:27.846263+00:00
-- url     : https://prove2.me/submissions/866162f5-7e31-48ca-82d3-db3ab2d00364

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HasDerivAtExpMul
import Theorems.Thm_GlobalTheory_CompanionTheory_WtLinkPf_hasDerivAt_exp_mul
import Theorems.Thm_CompanionTheory_D_DSIC_lift_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.DSIC.lift_apply



set_option autoImplicit false
open Matrix Finset
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.WtLinkPf
open PI.UpqRep
variable {n : ℕ}
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
namespace GlobalTheory.CompanionTheory.WtLinkPf
theorem _root_.solution (φ : ℝ → (H →L[ℂ] H)) (hadd : ∀ s t, φ (s + t) = φ s * φ t) (h0 : φ 0 = 1) (v : H) (c : ℂ)
    (hd : HasDerivAt (fun t => φ t v) (c • v) 0) : φ 1 v = Complex.exp c • v := by
  have hder : ∀ s : ℝ, HasDerivAt (fun t => φ t v) (c • φ s v) s := by
    intro s
    have h1 : HasDerivAt (fun u => φ s (φ u v)) (φ s (c • v)) 0 := by
      have := ((φ s).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd
      simpa [Function.comp_def] using this
    have h2 : HasDerivAt (fun u => φ s (φ u v)) (φ s (c • v)) (s - s) := by
      rwa [sub_self]
    have h3 := HasDerivAt.comp_sub_const s s h2
    rw [map_smul] at h3
    convert h3 using 1
    funext t
    show φ t v = φ s (φ (t - s) v)
    rw [← ContinuousLinearMap.mul_apply, ← hadd, show s + (t - s) = t by ring]
  have hg : ∀ s : ℝ, HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * -c) • φ t v) 0 s := by
    intro s
    have := (hasDerivAt_exp_mul (-c) s).smul (hder s)
    convert this using 1
    · funext t
      rfl
    · rw [smul_smul, ← add_smul]
      simp
  have hdiff : Differentiable ℝ (fun t : ℝ => Complex.exp ((t : ℂ) * -c) • φ t v) :=
    fun s => (hg s).differentiableAt
  have hconst := is_const_of_deriv_eq_zero hdiff (fun s => (hg s).deriv) 1 0
  have hfinal : Complex.exp (-c) • φ 1 v = v := by
    simp only [Complex.ofReal_one, Complex.ofReal_zero, one_mul, zero_mul, Complex.exp_zero, one_smul, h0,
      ContinuousLinearMap.one_apply] at hconst
    exact hconst
  calc φ 1 v = Complex.exp c • (Complex.exp (-c) • φ 1 v) := by
        rw [smul_smul, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_smul]
    _ = Complex.exp c • v := by rw [hfinal]
end GlobalTheory.CompanionTheory.WtLinkPf
