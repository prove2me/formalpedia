-- Prove2me | solution 1 for GlobalTheory.SW.HeatTerm.isHeat_of_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:10:49.392942+00:00
-- url     : https://prove2.me/submissions/eea33f9e-bc6f-40b8-b4f3-4c79d3a415f3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_DerivDerivConstMulCexpBilinearAtZero
import Theorems.Thm_GlobalTheory_SW_HeatTerm_diffAt_det
import Theorems.Thm_GlobalTheory_SW_HeatTerm_diffAt_inv
import Theorems.Thm_GlobalTheory_SW_HeatTerm_loc_heat
import Theorems.Thm_GlobalTheory_SW_HeatTerm_hFac_inv
import Theorems.Thm_GlobalTheory_SW_HeatTerm_hFac_inv_at

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.HeatTerm
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)) {n N : ℕ}
omit [NumberField E] [IsCMField E]
namespace GlobalTheory.SW.HeatTerm
theorem _root_.solution (γ : M2 E N) (h : ∀ Z ∈ Hn Ψ N, ∀ τ, (hDen Ψ γ Z τ).det ≠ 0) :
    IsHeat Ψ (fun Z (z z' : CM Ψ n N) => (hFac Ψ γ Z z z')⁻¹) := by
  classical
  refine ⟨fun p hp => DifferentiableAt.differentiableWithinAt ?_, fun Z hZ z z' τ a b => ?_⟩
  · suffices hs : ∀ τ : Ψ, DifferentiableAt ℂ (fun y : CF Ψ N N × CF Ψ n N × CF Ψ n N =>
        loc (n := n) (γ.toBlocks₂₁.map τ.1) (γ.toBlocks₂₂.map τ.1) (y.1 τ) (y.2.1 τ) (y.2.2 τ)) p by
      refine ((HasFDerivAt.finsetProd (u := Finset.univ)
        (fun τ _ => (hs τ).hasFDerivAt)).differentiableAt).congr_of_eventuallyEq ?_
      exact Filter.Eventually.of_forall fun y => hFac_inv Ψ γ _ _ _
    intro τ
    have hd := h _ hp τ
    have hM : ∀ i j, DifferentiableAt ℂ (fun y : CF Ψ N N × CF Ψ n N × CF Ψ n N =>
        hDen Ψ γ y.1 τ i j) p := by
      intro i j
      show DifferentiableAt ℂ (fun y : CF Ψ N N × CF Ψ n N × CF Ψ n N =>
        ∑ l, γ.toBlocks₂₁.map τ.1 i l * y.1 τ l j + γ.toBlocks₂₂.map τ.1 i j) p
      fun_prop
    have h1 := diffAt_det _ p hM
    have h2 := diffAt_inv _ p hM hd
    refine DifferentiableAt.fun_inv ((h1.fun_pow n).fun_mul (DifferentiableAt.cexp ?_))
      (mul_ne_zero (pow_ne_zero _ hd) (Complex.exp_ne_zero _))
    refine DifferentiableAt.const_mul (DifferentiableAt.fun_sum fun k _ => ?_) _
    simp only [dotProduct, Matrix.mulVec, Matrix.mul_apply]
    refine DifferentiableAt.fun_sum fun i _ => DifferentiableAt.fun_mul (by fun_prop) ?_
    refine DifferentiableAt.fun_sum fun j _ => DifferentiableAt.fun_mul ?_ (by fun_prop)
    exact DifferentiableAt.fun_sum fun l _ => (h2 i l).mul_const _
  · have e1 := fun s : ℂ => hFac_inv_at Ψ γ Z z z' τ (Matrix.single a b s) 0 0
    have e2 := fun (k : Fin n) (s t : ℂ) =>
      hFac_inv_at Ψ γ Z z z' τ 0 (Matrix.single k a s) (Matrix.single k b t)
    simp only [ite_self, add_zero] at e1 e2
    simp only [e1, e2]
    exact loc_heat _ _ _ _ _ (h Z hZ τ) a b _
end GlobalTheory.SW.HeatTerm
