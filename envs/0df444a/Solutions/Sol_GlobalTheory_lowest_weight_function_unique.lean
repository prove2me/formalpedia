-- Prove2me | solution 1 for GlobalTheory.lowest_weight_function_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:50:26.725299+00:00
-- url     : https://prove2.me/submissions/c74758d4-7acb-4712-955d-889a0735066d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthogonalFrameDomain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientDomain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_LowestWeightFunctionMulEq
import Theorems.Thm_GlobalTheory_LowestWeight_exists_lower
import Theorems.Thm_GlobalTheory_LowestWeight_finite_lminor
import Theorems.Thm_GlobalTheory_LowestWeight_eq_zero_lower
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FourierCoefficientDomain_isOpen_dom
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_OrthogonalFrameDomain_rmul_mem_dom


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open NumberField ReciprocityTheory.ChartRestriction.G.FD Matrix Filter Topology
open scoped ComplexConjugate ComplexOrder
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory
theorem _root_.solution {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) (x₀ : Frame X.Ψ r)
    (hx₀ : ∀ τ : X.Ψ, gram τ.1 X.Gm (mat x₀ τ) = Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) (hx₀' : x₀ ∈ X.dom)
    (m : Frame X.Ψ r → ℂ) (hm : DifferentiableOn ℂ m X.dom) (hB : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, m (rmul x b) = bchar la b * m x)
    (hT : ∀ t : X.Ψ → Fin r → ℂ, (∀ τ i, ‖t τ i‖ = 1) → ∀ x ∈ X.dom,
      m (X.lmulC (fun τ => mat x₀ τ * Matrix.diagonal (t τ) * (mat x₀ τ)⁻¹) x) = (∏ τ, ∏ i, t τ i ^ la τ i) * m x)
    (h0 : m x₀ = 0) : ∀ x ∈ X.dom, m x = 0 := by

  have hcell : ∀ y : Frame X.Ψ r, rmul x₀ y ∈ X.dom → (∀ τ i, lminor (mat y τ) i ≠ 0) →
      m (rmul x₀ y) = 0 := by
    intro y hy hmin
    choose B hB1 hB2 hB3 using fun τ => LowestWeight.exists_lower (mat y τ) (hmin τ)
    have hBb : (fun τ => B τ : Frame X.Ψ r) ∈ Bor X.Ψ r := by
      intro τ
      refine ⟨?_, hB2 τ⟩
      change (B τ).det ≠ 0
      rw [Matrix.det_of_isUpperTriangular (fun a c h => hB2 τ a c h)]
      simp [hB1]
    have e : rmul (rmul x₀ y) (fun τ => B τ) =
        rmul x₀ (fun τ => (mat y τ * B τ : Matrix (Fin r) (Fin r) ℂ)) := by
      funext τ
      exact Matrix.mul_assoc (mat x₀ τ) (mat y τ) (B τ)
    have h1 := hB _ hy _ hBb
    have h2 := OrthogonalFrameDomain.rmul_mem_dom X hy hBb
    rw [e] at h1 h2
    rw [LowestWeight.eq_zero_lower X la x₀ hx₀ hx₀' m hm hB hT h0 hB3 h2] at h1
    simpa [bchar, hB1] using h1.symm

  intro x hx
  set y : X.Ψ → Matrix (Fin r) (Fin r) ℂ := fun τ => (mat x₀ τ)⁻¹ * mat x τ with hy
  have e : ∀ s : ℂ, x + s • x₀ =
      rmul x₀ fun τ => (y τ + s • (1 : Matrix (Fin r) (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) := by
    intro s
    funext τ
    change mat x τ + s • mat x₀ τ = mat x₀ τ * ((mat x₀ τ)⁻¹ * mat x τ + s • 1)
    rw [Matrix.mul_add, Matrix.mul_nonsing_inv_cancel_left _ _ (isUnit_iff_ne_zero.2 (hx₀' τ).1),
      Matrix.mul_smul, Matrix.mul_one]
  have hlim : Tendsto (fun s : ℂ => x + s • x₀) (𝓝[≠] 0) (𝓝 x) :=
    (Continuous.tendsto' (by fun_prop) _ _ (by simp)).mono_left nhdsWithin_le_nhds
  have hn : X.dom ∈ 𝓝 x := (FourierCoefficientDomain.isOpen_dom X).mem_nhds hx
  have hgood : ∀ᶠ s : ℂ in 𝓝[≠] 0, ∀ τ i,
      lminor (y τ + s • (1 : Matrix (Fin r) (Fin r) ℂ)) i ≠ 0 := by
    simp only [eventually_all]
    intro τ i
    exact nhdsNE_le_cofinite _ (LowestWeight.finite_lminor (y τ) i).eventually_cofinite_notMem
  have hz : ∀ᶠ s : ℂ in 𝓝[≠] 0, m (x + s • x₀) = 0 := by
    filter_upwards [hgood, hlim.eventually hn] with s hs hsd
    rw [e s] at hsd ⊢
    exact hcell _ hsd hs
  exact tendsto_nhds_unique ((hm.differentiableAt hn).continuousAt.tendsto.comp hlim)
    (tendsto_const_nhds.congr' (hz.mono fun s hs => hs.symm))
end GlobalTheory
