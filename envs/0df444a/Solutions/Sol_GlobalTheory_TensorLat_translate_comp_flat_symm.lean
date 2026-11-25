-- Prove2me | solution 1 for GlobalTheory.TensorLat.translate_comp_flat_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:39:04.695738+00:00
-- url     : https://prove2.me/submissions/00e67cf5-5849-43b2-b68a-cd6c3c1e00ba

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_FlatMemLatIffStdLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_NsmulApplyMemOfMemTensorLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IntegrableOnFundamentalDomainOfContinuous
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsBasisSpanEqOfCommensurable
import Theorems.Thm_GlobalTheory_TensorLat_HC_flat_symm
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
open GlobalTheory GlobalTheory.TensorLat
open NumberField Complex ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.FD MeasureTheory
open ReciprocityTheory.GeometryOfNumbersTheory (stdLat)
variable {E : Type} [Field E] [NumberField E] {dim : (E →+* ℂ) → ℕ} {n : ℕ}
namespace GlobalTheory.TensorLat
theorem _root_.solution (X : PT E)
    (U : ℕ → EuclideanSpace ℂ (Fin n × Idx X.dim) → (EuclideanSpace ℂ (Fin n × Idx X.dim) → ℂ) →
      EuclideanSpace ℂ (Fin n × Idx X.dim) → ℂ)
    (hU : ∀ (q : ℕ) a F v,
      U q a F v = cexp (q * Real.pi * Hf v a - q * Real.pi * Hf a a / 2) * F (v - a))
    (q : ℕ) (a : Fin n → Vsp X.dim) (F : (Fin n → Vsp X.dim) → ℂ) :
    U q (flat a) (F ∘ flat.symm) = X.U q a F ∘ flat.symm := by
  funext v
  have e1 : Hf v (flat a) = HC (flat.symm v) a := by
    rw [← HC_flat_symm v (flat a), ContinuousLinearEquiv.symm_apply_apply]
  simp only [hU, Function.comp, PT.U, e1, Hf_flat, map_sub, ContinuousLinearEquiv.symm_apply_apply]
end GlobalTheory.TensorLat
