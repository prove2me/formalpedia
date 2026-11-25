-- Prove2me | solution 1 for GlobalTheory.ThetaBound.col_mem_Sec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:50:38.877039+00:00
-- url     : https://prove2.me/submissions/3cb70c79-2f59-41c3-8f30-cf948a77d0c4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_L2NormFundamentalDomain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtData
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_FlatMemLatIffStdLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_SupLeL2PrincipalTorus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CardToMultisetEqDegree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_PointwiseNormSqPullbackTensorEqProd
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
theorem _root_.solution (X : PT E) {q : ℕ} {s : (Fin 1 → Vsp X.dim) → ℂ} (hs : s ∈ X.Sec q 1) :
    (fun z => s fun _ => z) ∈ (gtOf X q).Sec q := by
  refine ⟨hs.1.comp (differentiable_pi.2 fun _ => differentiable_id), fun γ hγ v => ?_⟩
  have e : (fun _ : Fin 1 => v + γ) = (fun _ => v) + (fun _ => γ) := by funext j; simp
  simp only [e]
  rw [hs.2 (fun _ => γ) (fun _ => hγ) (fun _ => v)]
  simp [HC, gtOf]
end GlobalTheory.ThetaBound
