-- Prove2me | solution 1 for GlobalTheory.RealWeil.Vacuum.mean_value
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:07:45.309796+00:00
-- url     : https://prove2.me/submissions/5b37171f-9ccc-4295-9add-1284308c94fe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProjEqSelfOfAnnihilated
import Theorems.Thm_GlobalTheory_RealWeil_Vacuum_differentiable_norm
import Theorems.Thm_GlobalTheory_RealWeil_Vacuum_fderiv_norm_J
import Theorems.Thm_GlobalTheory_RealWeil_gau_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped RealInnerProductSpace ContDiff Real ComplexOrder
open GlobalTheory GlobalTheory.RealWeil GlobalTheory.RealWeil.Vacuum
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] {J : V ≃ₗᵢ[ℝ] V} {ρ : V → B →L[ℂ] B}
namespace GlobalTheory.RealWeil.Vacuum
theorem _root_.solution [CompleteSpace B] (hJ : ∀ x, J (J x) = -x) (h : IsHeis (omJ J) ρ) (f : B) (hf : Sm ρ f)
    (ha : ∀ z, fderiv ℝ (fun v => ρ v f) 0 z + I • fderiv ℝ (fun v => ρ v f) 0 (J z) = 0) (u : V) :
    ∫ θ in (0 : ℝ)..2 * π, (gau (line J u (circleMap 0 1 θ)))⁻¹ • ρ (line J u (circleMap 0 1 θ)) f =
      (2 * π) • f := by
  have hd : Differentiable ℂ fun ζ => (gau (line J u ζ))⁻¹ • ρ (line J u ζ) f := by
    intro ζ
    have h1 : HasFDerivAt (fun ζ => (gau (line J u ζ))⁻¹ • ρ (line J u ζ) f)
        ((fderiv ℝ (fun u => (gau u)⁻¹ • ρ u f) (line J u ζ)).comp (line J u)) ζ :=
      (differentiable_norm f hf _).hasFDerivAt.comp ζ (line J u).hasFDerivAt
    refine differentiableAt_complex_iff_differentiableAt_real.2 ⟨h1.differentiableAt, ?_⟩
    rw [h1.fderiv]
    simpa [line_apply] using fderiv_norm_J hJ h f hf ha (line J u ζ) u
  have := DiffContOnCl.circleAverage (c := 0) (R := 1) hd.diffContOnCl
  rw [Real.circleAverage_def] at this
  simp only [map_zero, gau_zero, h.1, inv_one, one_smul] at this
  conv_rhs => rw [← this]
  rw [smul_inv_smul₀ Real.two_pi_pos.ne']
end GlobalTheory.RealWeil.Vacuum
