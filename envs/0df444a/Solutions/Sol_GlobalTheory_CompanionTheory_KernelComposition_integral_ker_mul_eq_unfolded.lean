-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.KernelComposition.integral_ker_mul_eq_unfolded
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:40:56.375806+00:00
-- url     : https://prove2.me/submissions/b2a31c6a-3599-484b-b7b9-efd89f3911c8

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_ThetaCellCovers_KernelL2RowsColumns
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_KerMulOfKerBasicOfCvTest

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory PositivityTheory.Rg.BcB.E1
open scoped ENNReal Pointwise
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.KernelComposition
namespace GlobalTheory.CompanionTheory.KernelComposition
theorem _root_.solution (hk : KerBasic) (X : Ctx) (φ ψ : X.G → ℂ) (hφ : Tst φ)
    (hψ : Tst ψ) (x y : X.G) :
    ∫ z, ker X.Γ φ x z * ker X.Γ ψ z y ∂X.ν = ∫ z, φ (x⁻¹ * z) * ker X.Γ ψ z y ∂X.μ := by
  haveI : MeasurableConstSMul X.Γ X.G := ⟨fun γ => measurable_const_mul (γ : X.G)⟩
  haveI : SMulInvariantMeasure X.Γ X.G X.μ := ⟨fun γ s _ => measure_preimage_mul _ γ.1 s⟩
  set g : X.G → ℂ := fun z => φ (x⁻¹ * z) * ker X.Γ ψ z y with hg
  have hkc : Continuous fun z => ker X.Γ ψ z y :=
    (hk X ψ hψ).2.1.comp (continuous_id.prodMk continuous_const)
  have hgc : Continuous g := (hφ.1.comp (continuous_const.mul continuous_id)).mul hkc
  have hgs : HasCompactSupport g :=
    HasCompactSupport.mul_right (hφ.2.comp_homeomorph (Homeomorph.mulLeft x⁻¹))
  have hgi : Integrable g X.μ := hgc.integrable_of_hasCompactSupport hgs
  have hpt : ∀ z, ker X.Γ φ x z * ker X.Γ ψ z y = ∑' γ : X.Γ, g (γ • z) := by
    intro z
    have h1 : ∀ γ : X.Γ, g (γ • z) = φ (x⁻¹ * (γ : X.G) * z) * ker X.Γ ψ z y := by
      intro γ
      have h2 : γ • z = (γ : X.G) * z := rfl
      simp only [hg, h2, (hk X ψ hψ).2.2.1 γ γ.2 z y |>.1, mul_assoc]
    simp only [h1]
    rw [tsum_mul_right, ker, tsum_eq_finsum ((hk X φ hφ).1 x z)]
  have hmeas : ∀ γ : X.Γ, Continuous fun z => g (γ • z) := fun γ =>
    hgc.comp (continuous_const.mul continuous_id)
  have hfin : ∑' γ : X.Γ, ∫⁻ z, ‖g (γ • z)‖ₑ ∂X.ν ≠ ∞ := by
    have h3 : ∑' γ : X.Γ, ∫⁻ z, ‖g (γ • z)‖ₑ ∂X.ν = ∫⁻ z, ‖g z‖ₑ ∂X.μ :=
      (X.fd.lintegral_eq_tsum'' fun z => ‖g z‖ₑ).symm
    rw [h3]
    exact hgi.2.ne
  simp only [hpt]
  rw [integral_tsum (fun γ => (hmeas γ).aestronglyMeasurable) hfin]
  exact (X.fd.integral_eq_tsum'' g hgi).symm
end GlobalTheory.CompanionTheory.KernelComposition
