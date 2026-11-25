-- Prove2me | solution 1 for GlobalTheory.ThetaBound.norm_polyDeriv_U_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:59:08.662301+00:00
-- url     : https://prove2.me/submissions/62fd8691-6570-45cb-ae35-ce832336f26c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_L2NormFundamentalDomain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtData
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_FlatMemLatIffStdLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_SupLeL2PrincipalTorus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CardToMultisetEqDegree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_PointwiseNormSqPullbackTensorEqProd
import Theorems.Thm_GlobalTheory_ThetaBound_norm_polyDeriv_le
import Theorems.Thm_GlobalTheory_Jet_differentiable_translate
import Theorems.Thm_GlobalTheory_Jet_norm_polyDeriv_le
import Theorems.Thm_GlobalTheory_Jet_norm_translate
import Theorems.Thm_GlobalTheory_Jet_polyDeriv_comp_equiv
import Theorems.Thm_GlobalTheory_TensorLat_HC_self_re
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_actE_apply
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
open Complex ReciprocityTheory.ChartRestriction.G.I2
open GlobalTheory
open GlobalTheory.ThetaBound
open TensorLat
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.ThetaBound
theorem _root_.solution (X : PT E) (q : ℕ) {n : ℕ} (F : (Fin n → Vsp X.dim) → ℂ)
    (hF : Differentiable ℂ F) (S : ℝ) (hS : ∀ v, X.ptN2 q F v ≤ S)
    (P : MvPolynomial (Letter n X.dim) ℂ) (a : ℕ) (hP : P.IsHomogeneous a)
    (b : Fin n → Vsp X.dim) :
    ‖polyDeriv P dir (X.U q b F) 0‖ ≤
      (∑ m ∈ P.support, ‖P.coeff m‖) * Real.sqrt S *
        (q * Real.pi * Real.exp 1 * a) ^ ((a : ℝ) / 2) := by
  set G : EuclideanSpace ℂ (Fin n × Idx X.dim) → ℂ := F ∘ flat.symm with hG
  have hGd : Differentiable ℂ G := hF.comp (flat (n := n) (ι := Idx X.dim)).symm.differentiable
  have e : X.U q b F = (fun v => cexp (q * Real.pi * Hf v (flat b) -
      q * Real.pi * Hf (flat b) (flat b) / 2) * G (v - flat b)) ∘ flat := by
    funext v
    simp only [PT.U, Function.comp, hG, Hf_flat, ← map_sub,
      ContinuousLinearEquiv.symm_apply_apply]
  have h := norm_polyDeriv_le q _ (Jet.differentiable_translate q (flat b) hGd) S
    (fun v => by
      rw [Jet.norm_translate]
      have h1 := hS (flat.symm (v - flat b))
      rwa [PT.ptN2, HC_self_re, ContinuousLinearEquiv.apply_symm_apply] at h1) P a hP
  rw [e, Jet.polyDeriv_comp_equiv, map_zero]
  convert h using 3
  funext l
  rw [Function.comp_apply]
  convert flat_dir l
end GlobalTheory.ThetaBound
