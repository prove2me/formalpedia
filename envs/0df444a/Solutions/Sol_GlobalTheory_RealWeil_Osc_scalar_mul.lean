-- Prove2me | solution 1 for GlobalTheory.RealWeil.Osc.scalar_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:57:12.901311+00:00
-- url     : https://prove2.me/submissions/00420701-c737-4c2c-ba86-58c6f6778935

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralGauTwistedConv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PowMulNormGauLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOscillatorActionOfGaussianPairings
import Theorems.Thm_GlobalTheory_RealWeil_Osc_proj_proj
import Theorems.Thm_GlobalTheory_RealWeil_Osc_proj_twist_proj
import Theorems.Thm_GlobalTheory_RealWeil_Osc_proj_twist_twist_proj
import Theorems.Thm_GlobalTheory_RealWeil_Osc_k_inv
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
theorem _root_.solution (hl : ∀ g, star (c g) * c g * lam (k g) = 1)
    (hm : ∀ g g', c g * c g' * mu J (k (g * g')) (k g) = c (g * g') * lam (k (g * g'))) (g g' : G) (x : B) :
    (c g * c g') • pr h hk (g * g') (pr h hk g (proj h x)) = c (g * g') • pr h hk (g * g') (proj h x) := by
  rw [← sub_eq_zero]
  set y := (c g * c g') • pr h hk (g * g') (pr h hk g (proj h x)) - c (g * g') • pr h hk (g * g') (proj h x) with hy
  have h1 : proj h y = 0 := by
    rw [hy, map_sub, map_smul, map_smul, proj_twist_twist_proj hJ h _ _ (hk _) (hk _),
      proj_twist_proj hJ h _ (k (g * g')) (fun _ => rfl), smul_smul, smul_smul, hm, sub_self]
  have h2 : pr h hk (g * g') y = y := by
    simp only [hy, map_sub, map_smul, proj_proj hJ]
  have h3 := proj_twist_proj hJ (h.twist (k (g * g')) (hk _)) h (k (g * g')⁻¹) (fun u => by simp only [k_inv]) y
  have h4 : lam (k (g * g')⁻¹) ≠ 0 := fun e => by
    have := hl (g * g')⁻¹
    rw [e, mul_zero] at this
    exact zero_ne_one this
  rw [h2, h1, map_zero] at h3
  exact (smul_eq_zero.1 h3.symm).resolve_left h4
end GlobalTheory.RealWeil.Osc
