-- Prove2me | solution 1 for GlobalTheory.RealWeil.Osc.exists_isOsc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:05:20.853865+00:00
-- url     : https://prove2.me/submissions/ddea02df-5bbb-4885-bcf0-d0456c721d93

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralGauTwistedConv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PowMulNormGauLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOscillatorActionOfGaussianPairings
import Theorems.Thm_GlobalTheory_RealWeil_Osc_good_of_sm
import Theorems.Thm_GlobalTheory_RealWeil_Osc_intw_add
import Theorems.Thm_GlobalTheory_RealWeil_Osc_intw_smul
import Theorems.Thm_GlobalTheory_RealWeil_Osc_proj_comm
import Theorems.Thm_GlobalTheory_RealWeil_Osc_intw_comm
import Theorems.Thm_GlobalTheory_RealWeil_Osc_continuous_twist_intw
import Theorems.Thm_GlobalTheory_RealWeil_Osc_proj_twist_of_isometry
import Theorems.Thm_GlobalTheory_RealWeil_Osc_k_inv
import Theorems.Thm_GlobalTheory_RealWeil_Osc_vacOp_apply
import Theorems.Thm_GlobalTheory_RealWeil_Osc_pr_one
import Theorems.Thm_GlobalTheory_RealWeil_Osc_vacOp_proj
import Theorems.Thm_GlobalTheory_RealWeil_Osc_sm_osc
import Theorems.Thm_GlobalTheory_RealWeil_Osc_osc_heis
import Theorems.Thm_GlobalTheory_RealWeil_Osc_osc_pr
import Theorems.Thm_GlobalTheory_RealWeil_Osc_osc_proj
import Theorems.Thm_GlobalTheory_RealWeil_Osc_osc_one
import Theorems.Thm_GlobalTheory_RealWeil_Osc_osc_mul
import Theorems.Thm_GlobalTheory_RealWeil_Osc_norm_osc
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
namespace GlobalTheory.RealWeil.Osc
theorem _root_.solution : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] (J : V ≃ₗᵢ[ℝ] V) (ρ : V → B →L[ℂ] B), (∀ x, J (J x) = -x) → ∀ h : IsHeis (omJ J) ρ, ∀ (G : Type) [Group G] (k : G →* (V →L[ℝ] V)) (c : G → ℂ), (∀ g x y, omJ J (k g x) (k g y) = omJ J x y) → c 1 = 1 → (∀ g, star (c g) * c g * lam (k g) = 1) → (∀ g g', c g * c g' * mu J (k (g * g')) (k g) = c (g * g') * lam (k (g * g'))) → ∃ Ω : G → B → B, IsOsc ρ (fun g v => k g v) Ω ∧ (∀ (Y : Type) [TopologicalSpace Y] (γ : Y → G), Continuous (fun y => k (γ y)) → Continuous (fun y => c (γ y)) → ∀ f, Sm ρ f → Continuous fun y => Ω (γ y) f) ∧ ∀ a g, (∀ x, ‖k g x‖ = ‖x‖) → ∀ f, Sm ρ f → ∫ u, gau u • ρ (k a u) f = f → Ω (a * g * a⁻¹) f = c g • f := by
  intro V _ _ _ _ _ B _ _ _ J ρ hJ h G _ k c hk hc hl hm
  refine ⟨osc h hk c, ⟨fun g f f' hf hf' => ?_, fun g a f _ => intw_smul a f, fun g f hf => sm_osc hJ h hk g hf,
    fun f hf => osc_one hJ h hk hc hf, fun g g' f hf => osc_mul hJ h hk hl hm g g' hf,
    fun g v f hf => osc_heis hJ h hk g v hf, fun g A hA f hf => ?_,
    fun H _ _ _ Φ hΦ g f hf => norm_osc hJ h hk hl Φ hΦ g hf⟩, fun Y _ γ hγ hcγ f hf => ?_,
    fun a g hg f hf hfa => ?_⟩
  · exact intw_add (h.twist (k g) (hk g)) (vacOp_proj hJ h hk g) (good_of_sm hJ h hf) (good_of_sm hJ h hf')
  · refine intw_comm (h.twist (k g) (hk g)) (vacOp_proj hJ h hk g) (good_of_sm hJ h hf) A hA (fun v => hA _)
      fun x => ?_
    rw [vacOp_apply, vacOp_apply, map_smul, proj_comm (h.twist (k g) (hk g)) A (fun v => hA _), proj_comm h A hA]
  · refine (hcγ.smul ((continuous_twist_intw (good_of_sm hJ h hf)).comp hγ)).congr fun y => ?_
    simp only [osc, intw, vacOp_apply, map_smul, integral_smul]
    rfl
  · have hfa' : pr h hk a f = f := hfa
    have s0 := sm_osc (c := c) hJ h hk a⁻¹ hf
    have e0 : proj h (osc h hk c a⁻¹ f) = osc h hk c a⁻¹ f := by
      rw [← pr_one h hk, ← inv_mul_cancel a, ← osc_pr hJ h hk _ _ hf, hfa']
    have e1 : osc h hk c g (osc h hk c a⁻¹ f) = c g • osc h hk c a⁻¹ f := by
      have := osc_proj (c := c) hJ h hk g s0
      rw [proj_twist_of_isometry h (k g) (k g⁻¹) (k_inv k g) (hk g) hg, e0, e0] at this
      exact this
    rw [osc_mul hJ h hk hl hm _ _ hf, osc_mul hJ h hk hl hm _ _ s0, e1, osc, intw_smul, ← osc,
      ← osc_mul hJ h hk hl hm _ _ hf, mul_inv_cancel, osc_one hJ h hk hc hf]
end GlobalTheory.RealWeil.Osc
