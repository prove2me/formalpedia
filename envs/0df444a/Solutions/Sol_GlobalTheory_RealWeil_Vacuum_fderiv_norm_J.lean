-- Prove2me | solution 1 for GlobalTheory.RealWeil.Vacuum.fderiv_norm_J
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:14:04.653419+00:00
-- url     : https://prove2.me/submissions/84231b5c-9016-44b6-88da-c9f8b00eb33f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProjEqSelfOfAnnihilated
import Theorems.Thm_GlobalTheory_RealWeil_Vacuum_fderiv_norm

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
theorem _root_.solution (hJ : ∀ x, J (J x) = -x) (h : IsHeis (omJ J) ρ) (f : B) (hf : Sm ρ f)
    (ha : ∀ z, fderiv ℝ (fun v => ρ v f) 0 z + I • fderiv ℝ (fun v => ρ v f) 0 (J z) = 0) (u z : V) :
    fderiv ℝ (fun u => (gau u)⁻¹ • ρ u f) u (J z) = I • fderiv ℝ (fun u => (gau u)⁻¹ • ρ u f) u z := by
  have e : fderiv ℝ (fun v => ρ v f) 0 (J z) = I • fderiv ℝ (fun v => ρ v f) 0 z := by
    rw [eq_neg_of_add_eq_zero_left (ha z), smul_neg, smul_smul, I_mul_I]
    simp
  rw [fderiv_norm h f hf, fderiv_norm h f hf, e, map_smul, smul_add, smul_comm I, smul_smul I, hJ, inner_neg_right]
  congr 2
  push_cast
  linear_combination (gau u)⁻¹ * π * (⟪u, J z⟫ : ℝ) * I_mul_I
end GlobalTheory.RealWeil.Vacuum
