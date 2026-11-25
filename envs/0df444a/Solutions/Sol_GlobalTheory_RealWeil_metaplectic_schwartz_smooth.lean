-- Prove2me | solution 1 for GlobalTheory.RealWeil.metaplectic_schwartz_smooth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:55:37.830122+00:00
-- url     : https://prove2.me/submissions/a4489b73-e530-4024-a114-ff847cc1200b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IteratedLineDerivMemWeylAlg
import Theorems.Thm_GlobalTheory_RealWeil_exists_factor
import Theorems.Thm_GlobalTheory_RealWeil_omS_dRho
import Theorems.Thm_GlobalTheory_RealWeil_contDiff_toLp_omS
import Theorems.Thm_GlobalTheory_RealWeil_hasDerivAt_toLp_omS

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap LineDeriv Matrix
open scoped Real RealInnerProductSpace ContDiff FourierTransform
open GlobalTheory GlobalTheory.RealWeil
variable {l : Type} [Fintype l]
variable [DecidableEq l]
variable {G : Type} [Group G] {pr : G →* Matrix.symplecticGroup l ℝ} {om : G →* (L2 l ≃ₗᵢ[ℂ] L2 l)}
  {omS : G →* (Sch l →L[ℂ] Sch l)}
namespace GlobalTheory.RealWeil
theorem _root_.solution [TopologicalSpace G]
    (h3 : ∀ (g : G) (w : l ⊕ l → ℝ) (f : L2 l),
      om g (rho w f) = rho ((pr g : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w) (om g f))
    (h4 : ∀ (g : G) (f : Sch l), om g (f.toLp 2 volume) = (omS g f).toLp 2 volume)
    (h5 : ∀ (k : ℕ) (γ : (Fin k → ℝ) → G), Continuous γ →
      (∀ a b, ContDiff ℝ ∞ fun t => (pr (γ t) : Matrix (l ⊕ l) (l ⊕ l) ℝ) a b) →
      ∀ f : Sch l, ContDiff ℝ ∞ fun t => om (γ t) (f.toLp 2 volume)) :
    (∀ (g : G) (w : l ⊕ l → ℝ) (f : Sch l),
      omS g (dRho w f) = dRho ((pr g : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w) (omS g f)) ∧
    (∀ (lam : Sch l →L[ℂ] ℂ) (k : ℕ) (γ : (Fin k → ℝ) → G), Continuous γ →
      (∀ a b, ContDiff ℝ ∞ fun t => (pr (γ t) : Matrix (l ⊕ l) (l ⊕ l) ℝ) a b) →
      ∀ f : Sch l, ContDiff ℝ ∞ fun t => lam (omS (γ t) f)) ∧
    (∀ (lam : Sch l →L[ℂ] ℂ), ∀ X ∈ LieAlgebra.Symplectic.sp l ℝ, ∀ γ : ℝ → G, γ 0 = 1 →
      (∀ t, (pr (γ t) : Matrix (l ⊕ l) (l ⊕ l) ℝ) = NormedSpace.exp (t • X)) →
      (∀ f : Sch l, HasDerivAt (fun t => om (γ t) (f.toLp 2 volume)) ((quad X f).toLp 2 volume) 0) →
      ∀ f : Sch l, HasDerivAt (fun t => lam (omS (γ t) f)) (lam (quad X f)) 0) := by
  refine ⟨omS_dRho h3 h4, fun lam k γ hc hγ f => ?_, fun lam X hX γ h0 hγ h6 f => ?_⟩
  · obtain ⟨ι, _, A, Λ, hA, h⟩ := exists_factor lam
    simp only [h]
    exact (Λ.restrictScalars ℝ).contDiff.comp
      (contDiff_pi.2 fun i => contDiff_toLp_omS h3 h4 hγ (h5 k γ hc hγ) (hA i) f)
  · obtain ⟨ι, _, A, Λ, hA, h⟩ := exists_factor lam
    simp only [h]
    exact (Λ.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0
      (hasDerivAt_pi.2 fun i => hasDerivAt_toLp_omS h3 h4 hX h0 hγ h6 (hA i) f)
end GlobalTheory.RealWeil
