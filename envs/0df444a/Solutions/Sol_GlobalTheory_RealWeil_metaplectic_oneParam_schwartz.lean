-- Prove2me | solution 1 for GlobalTheory.RealWeil.metaplectic_oneParam_schwartz
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:02:47.90551+00:00
-- url     : https://prove2.me/submissions/c68b68c8-8a1f-46a6-a286-19af80208117

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IteratedLineDerivMemWeylAlg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MetaplecticOneParameterSchwartzIntertwining
import Theorems.Thm_GlobalTheory_RealWeil_integral_norm_sq_eq_norm_toLp_sq
import Theorems.Thm_GlobalTheory_RealWeil_coeFn_rho
import Theorems.Thm_GlobalTheory_RealWeil_metaplectic_schwartz_smooth


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.RealWeil MeasureTheory
open scoped SchwartzMap Matrix
open GlobalTheory GlobalTheory.RealWeil
namespace GlobalTheory.RealWeil
theorem _root_.solution : GlobalTheory.Published.RealMetaplecticRepresentation →
    ∀ (l : Type) [Fintype l] [DecidableEq l] [Nonempty l] (X : Matrix (l ⊕ l) (l ⊕ l) ℝ),
      X ∈ LieAlgebra.Symplectic.sp l ℝ → ∃ U : ℝ → Sch l →ₗ[ℂ] Sch l, (∀ s t f, U (s + t) f = U s (U t f)) ∧
        (∀ f, U 0 f = f) ∧
        (∀ t w (f f₁ : Sch l), ⇑f₁ = rhoFun w ⇑f → ⇑(U t f₁) = rhoFun (NormedSpace.exp (t • X) *ᵥ w) ⇑(U t f)) ∧
        (∀ t f, ∫ x, ‖U t f x‖ ^ 2 = ∫ x, ‖f x‖ ^ 2) ∧ ∀ f y, HasDerivAt (fun t => U t f y) (quad X f y) 0 := by
  intro hMp l _ _ _ X hX
  obtain ⟨G, _, _, _, pr, om, omS, -, -, h3, h4, h5, h6⟩ := hMp l
  obtain ⟨γ, -, h0, hadd, hpr, hd⟩ := h6 X hX
  refine ⟨fun t => (omS (γ t)).toLinearMap, ?_, ?_, ?_, ?_, ?_⟩
  · intro s t f
    simp only [ContinuousLinearMap.coe_coe, hadd, map_mul, ContinuousLinearMap.mul_apply]
  · intro f
    simp [h0]
  · intro t w f f₁ h
    simp only [ContinuousLinearMap.coe_coe]
    rw [← hpr t]
    have hL : f₁.toLp 2 = rho w (f.toLp 2) := by
      refine Lp.ext ((SchwartzMap.coeFn_toLp f₁ 2 volume).trans ?_)
      refine Filter.EventuallyEq.symm ((coeFn_rho w _).trans ?_)
      rw [h]
      exact rhoFun_congr w (SchwartzMap.coeFn_toLp f 2 volume)
    have key : (omS (γ t) f₁).toLp 2 =
        rho ((pr (γ t) : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w) ((omS (γ t) f).toLp 2) := by
      rw [← h4, hL, h3, h4]
    have hae : ⇑(omS (γ t) f₁) =ᵐ[volume]
        rhoFun ((pr (γ t) : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w) ⇑(omS (γ t) f) := by
      refine (SchwartzMap.coeFn_toLp (omS (γ t) f₁) 2 volume).symm.trans ?_
      rw [key]
      refine (coeFn_rho _ _).trans ?_
      exact rhoFun_congr _ (SchwartzMap.coeFn_toLp (omS (γ t) f) 2 volume)
    have hc : Continuous (rhoFun ((pr (γ t) : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w) ⇑(omS (γ t) f)) :=
      (continuous_phase _).mul ((omS (γ t) f).continuous.comp (continuous_id.add continuous_const))
    exact (Continuous.ae_eq_iff_eq volume (omS (γ t) f₁).continuous hc).1 hae
  · intro t f
    simp only [ContinuousLinearMap.coe_coe]
    rw [integral_norm_sq_eq_norm_toLp_sq, integral_norm_sq_eq_norm_toLp_sq, ← h4, LinearIsometryEquiv.norm_map]
  · intro f y
    let lam : Sch l →L[ℂ] ℂ :=
      (BoundedContinuousFunction.evalCLM ℂ y).comp (SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ)
    have hlam : ∀ g : Sch l, lam g = g y := fun g => rfl
    have := (metaplectic_schwartz_smooth h3 h4 h5).2.2 lam X hX γ h0 hpr hd f
    simpa only [hlam, ContinuousLinearMap.coe_coe] using this
end GlobalTheory.RealWeil
