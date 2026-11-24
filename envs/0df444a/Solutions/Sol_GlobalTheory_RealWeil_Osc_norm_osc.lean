-- Prove2me | solution 1 for GlobalTheory.RealWeil.Osc.norm_osc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:23:30.3033+00:00
-- url     : https://prove2.me/submissions/896b9874-5efd-436b-86ed-439db17073ea

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralGauTwistedConv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PowMulNormGauLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOscillatorActionOfGaussianPairings
import Theorems.Thm_GlobalTheory_RealWeil_Osc_proj_proj
import Theorems.Thm_GlobalTheory_RealWeil_Osc_good_of_sm
import Theorems.Thm_GlobalTheory_RealWeil_Osc_proj_twist_proj
import Theorems.Thm_GlobalTheory_RealWeil_Osc_inner_proj
import Theorems.Thm_GlobalTheory_RealWeil_Osc_norm_intw
import Theorems.Thm_GlobalTheory_RealWeil_Osc_vacOp_apply
import Theorems.Thm_GlobalTheory_RealWeil_Osc_vacOp_proj
import Theorems.Thm_GlobalTheory_RealWeil_Osc_proj_vacOp
import Theorems.Thm_GlobalTheory_RealWeil_IsHeis_twist


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
open GlobalTheory GlobalTheory.RealWeil GlobalTheory.RealWeil.Osc
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] {J : V ≃ₗᵢ[ℝ] V}
  {ρ ρ' : V → B →L[ℂ] B}
set_option linter.unusedSectionVars false
variable {T : B →L[ℂ] B}
variable {G : Type} [Group G] {k : G →* (V →L[ℝ] V)} {c : G → ℂ}
variable (hJ : ∀ x, J (J x) = -x) (h : IsHeis (omJ J) ρ) (hk : ∀ g x y, omJ J (k g x) (k g y) = omJ J x y)
include hJ
namespace GlobalTheory.RealWeil.Osc
theorem _root_.solution (hl : ∀ g, star (c g) * c g * lam (k g) = 1) {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (Φ : B →L[ℂ] H) (hΦ : ∀ v f, ‖Φ (ρ v f)‖ = ‖Φ f‖) (g : G) {f : B}
    (hf : Sm ρ f) : ‖Φ (osc h hk c g f)‖ = ‖Φ f‖ := by
  refine norm_intw hJ (h.twist (k g) (hk g)) hΦ (fun v => hΦ _) (vacOp_proj hJ h hk g) (proj_vacOp hJ h hk g)
    (fun x => ?_) (good_of_sm hJ h hf)
  have e : inner ℂ (Φ (pr h hk g (proj h x))) (Φ (pr h hk g (proj h x))) =
      lam (k g) * inner ℂ (Φ (proj h x)) (Φ (proj h x)) := by
    rw [inner_proj hJ (h.twist (k g) (hk g)) (fun v => hΦ _), proj_proj hJ, inner_proj hJ h hΦ,
      proj_twist_proj hJ h _ (k g) (fun _ => rfl), map_smul, inner_smul_right, inner_proj hJ h hΦ, proj_proj hJ]
  rw [vacOp_apply, map_smul, inner_smul_left, inner_smul_right, e, ← mul_assoc, ← mul_assoc]
  exact (congrArg (· * _) (hl g)).trans (one_mul _)
end GlobalTheory.RealWeil.Osc
