-- Prove2me | solution 1 for GlobalTheory.TensorLat.im_HC_act_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:25:58.691276+00:00
-- url     : https://prove2.me/submissions/5caffc91-7a2b-4793-9c40-9d4db05d361e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_FlatMemLatIffStdLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_NsmulApplyMemOfMemTensorLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IntegrableOnFundamentalDomainOfContinuous
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsBasisSpanEqOfCommensurable
import Theorems.Thm_GlobalTheory_TensorLat_HC_actE
import Theorems.Thm_GlobalTheory_TensorLat_HC_add_left
import Theorems.Thm_GlobalTheory_TensorLat_HC_add_right
import Theorems.Thm_GlobalTheory_TensorLat_HC_conj
import Theorems.Thm_GlobalTheory_TensorLat_actE_coe
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_actE_add_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_actE_add_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_actE_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_actE_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_dim
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.I2.actE_apply



set_option autoImplicit false
open GlobalTheory GlobalTheory.TensorLat
open NumberField Complex ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.FD MeasureTheory
open ReciprocityTheory.GeometryOfNumbersTheory (stdLat)
variable {E : Type} [Field E] [NumberField E] {dim : (E →+* ℂ) → ℕ} {n : ℕ}
variable [IsCMField E]
namespace GlobalTheory.TensorLat
theorem _root_.solution (w₀ : 𝓞 E) (hw : (w₀ : E) + cc (w₀ : E) = 1) (γ δ : Fin n → Vsp dim) :
    (HC (γ + δ) fun k => act w₀ ((γ + δ) k)).im =
      (HC γ fun k => act w₀ (γ k)).im + (HC δ fun k => act w₀ (δ k)).im +
        (2 * (HC γ fun k => act w₀ (δ k)).im - (HC γ δ).im) := by
  have hact : ∀ v : Vsp dim, act w₀ v = actE (w₀ : E) v := fun v => (actE_coe w₀ v).symm
  simp only [hact]
  have hsplit : (fun k => actE (w₀ : E) ((γ + δ) k)) =
      (fun k => actE (w₀ : E) (γ k)) + (fun k => actE (w₀ : E) (δ k)) := by
    funext k
    simp only [Pi.add_apply, actE_add_right]
  have h1 : HC δ (fun k => actE (w₀ : E) (γ k)) =
      starRingEnd ℂ (HC γ (fun k => actE (cc (w₀ : E)) (δ k))) := by
    rw [HC_conj (fun k => actE (w₀ : E) (γ k)) δ, HC_actE]
  have h3 : HC γ δ = HC γ (fun k => actE (cc (w₀ : E)) (δ k)) +
      HC γ (fun k => actE (w₀ : E) (δ k)) := by
    rw [← HC_add_right]
    congr 1
    funext k
    rw [Pi.add_apply, ← actE_add_left, show cc (w₀ : E) + w₀ = 1 by rw [add_comm]; exact hw,
      actE_one]
  rw [hsplit, HC_add_left, HC_add_right, HC_add_right, h1]
  have h3' := congrArg Complex.im h3
  simp only [Complex.add_im] at h3'
  simp only [Complex.add_im, Complex.conj_im]
  linarith
end GlobalTheory.TensorLat
