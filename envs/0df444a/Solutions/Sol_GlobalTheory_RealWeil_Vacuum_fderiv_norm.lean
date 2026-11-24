-- Prove2me | solution 1 for GlobalTheory.RealWeil.Vacuum.fderiv_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:52:56.560539+00:00
-- url     : https://prove2.me/submissions/261243b8-a7e9-4e34-a20a-f87d67b1cbf5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProjEqSelfOfAnnihilated
import Theorems.Thm_GlobalTheory_RealWeil_Vacuum_differentiable_norm

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
theorem _root_.solution (h : IsHeis (omJ J) ρ) (f : B) (hf : Sm ρ f) (u z : V) :
    fderiv ℝ (fun u => (gau u)⁻¹ • ρ u f) u z =
      (gau u)⁻¹ • ρ u (fderiv ℝ (fun v => ρ v f) 0 z) +
        ((gau u)⁻¹ * (π * (⟪u, z⟫ : ℝ) - π * I * (⟪u, J z⟫ : ℝ))) • ρ u f := by
  have hl : HasDerivAt (fun s : ℝ => u + s • z) z 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const z).const_add u
  have hl0 : HasDerivAt (fun s : ℝ => s • z) z 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const z)
  have h1 : HasDerivAt (fun s : ℝ => (gau (u + s • z))⁻¹ • ρ (u + s • z) f)
      (fderiv ℝ (fun u => (gau u)⁻¹ • ρ u f) u z) 0 :=
    (differentiable_norm f hf u).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)
  have h2 : HasDerivAt (fun s : ℝ => ρ (s • z) f) (fderiv ℝ (fun v => ρ v f) 0 z) 0 :=
    ((ContDiff.differentiable hf (by simp)) 0).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hl0 (by simp)
  have h3 : HasDerivAt (fun s : ℝ => ρ u (ρ (s • z) f)) (ρ u (fderiv ℝ (fun v => ρ v f) 0 z)) 0 :=
    ((ρ u).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h2
  set c : ℂ := π * (⟪u, z⟫ : ℝ) - π * I * (⟪u, J z⟫ : ℝ) with hc
  have h4 : HasDerivAt (fun s : ℂ => (gau u)⁻¹ * cexp (c * s + (π / 2 * ‖z‖ ^ 2) * s ^ 2)) ((gau u)⁻¹ * c) 0 := by
    have := ((((hasDerivAt_id (0 : ℂ)).const_mul c).add
      (((hasDerivAt_id (0 : ℂ)).pow 2).const_mul (π / 2 * ‖z‖ ^ 2 : ℂ))).cexp).const_mul (gau u)⁻¹
    simpa using this
  have h5 : HasDerivAt (fun s : ℝ => (gau u)⁻¹ * cexp (c * s + (π / 2 * ‖z‖ ^ 2) * s ^ 2)) ((gau u)⁻¹ * c) 0 :=
    HasDerivAt.comp_ofReal (z := 0) (by rw [ofReal_zero]; exact h4)
  have h6 := h5.smul h3
  have e : (fun s : ℝ => (gau (u + s • z))⁻¹ • ρ (u + s • z) f) =
      (fun s : ℝ => (gau u)⁻¹ * cexp (c * s + (π / 2 * ‖z‖ ^ 2) * s ^ 2)) • fun s : ℝ => ρ u (ρ (s • z) f) := by
    funext s
    simp only [Pi.smul_apply', h.2.1, smul_smul]
    congr 1
    have n : ((‖u + s • z‖ : ℝ) : ℂ) ^ 2 = (‖u‖ : ℂ) ^ 2 + 2 * s * (⟪u, z⟫ : ℝ) + s ^ 2 * ‖z‖ ^ 2 := by
      have : ‖u + s • z‖ ^ 2 = ‖u‖ ^ 2 + 2 * s * ⟪u, z⟫ + s ^ 2 * ‖z‖ ^ 2 := by
        rw [norm_add_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]; ring
      exact_mod_cast this
    have o : omJ J u (s • z) = s * ⟪u, J z⟫ := by simp [omJ, inner_smul_right]
    rw [gau, gau, n, o, ← Complex.exp_neg, ← Complex.exp_neg, ← Complex.exp_add, ← Complex.exp_add, hc]
    congr 1
    push_cast
    ring
  rw [← e] at h6
  rw [h1.unique h6]
  simp [h.1]
end GlobalTheory.RealWeil.Vacuum
