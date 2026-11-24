-- Prove2me | solution 1 for GlobalTheory.HeightCont.height_continuousOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:43:45.997818+00:00
-- url     : https://prove2.me/submissions/306fc372-1055-44ac-ba42-dc5dc1bafe4b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsBasisMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_LatticeHeightContinuousOnFrames
import Theorems.Thm_GlobalTheory_LatBasis_exists_basis_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
open GlobalTheory GlobalTheory.HeightCont
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.HeightCont
theorem _root_.solution : (∀ (r : ℕ) (X : Data E r) (d : Frame X.Ψ r → Submodule E (Fin r → E) → ℝ), (∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (w : ι → Fin r → E), LinearIndependent E w → (∀ a, w a ∈ X.Λ) → d x (Submodule.span E (Set.range w)) = ((∏ τ : X.Ψ, ((((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))ᴴ * ((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))).det.re)) / (((Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup)) : ℝ))) → ∀ W, ContinuousOn (fun x => d x W) {x : Frame X.Ψ r | (∀ τ : X.Ψ, (mat x τ).det ≠ 0)}) := by
  intro r X d hd W
  obtain ⟨w, hw, hΛ, hsp⟩ := GlobalTheory.LatBasis.exists_basis_mem r X W
  suffices H : ContinuousOn (fun x => d x (Submodule.span E (Set.range w)))
      {x : Frame X.Ψ r | (∀ τ : X.Ψ, (mat x τ).det ≠ 0)} by rwa [hsp] at H
  refine ContinuousOn.congr ?_ (fun x hx => hd x hx _ w hw hΛ)
  refine ContinuousOn.div_const ?_ _
  refine continuousOn_finset_prod _ fun τ _ x hx => ContinuousAt.continuousWithinAt ?_
  have hm : Continuous (fun x : Frame X.Ψ r => mat x τ) := continuous_apply τ
  have hr : ContinuousAt (Ring.inverse : ℂ → ℂ) (mat x τ).det := by
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ (hx τ)
  have hi : ContinuousAt (fun x : Frame X.Ψ r => (mat x τ)⁻¹) x :=
    ContinuousAt.comp (f := fun x : Frame X.Ψ r => mat x τ) (continuousAt_matrix_inv _ hr)
      hm.continuousAt
  have hg : Continuous (fun A : Matrix (Fin r) (Fin r) ℂ =>
      ((A * (Matrix.of fun k a => τ.1 (w a k)))ᴴ * (A * (Matrix.of fun k a => τ.1 (w a k)))).det.re) :=
    Complex.continuous_re.comp
      (((continuous_id.matrix_mul continuous_const).matrix_conjTranspose.matrix_mul
        (continuous_id.matrix_mul continuous_const)).matrix_det)
  exact ContinuousAt.comp (f := fun x : Frame X.Ψ r => (mat x τ)⁻¹) hg.continuousAt hi
end GlobalTheory.HeightCont
