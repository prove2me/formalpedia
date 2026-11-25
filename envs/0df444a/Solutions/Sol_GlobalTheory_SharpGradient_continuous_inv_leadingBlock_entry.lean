-- Prove2me | solution 1 for GlobalTheory.SharpGradient.continuous_inv_leadingBlock_entry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:34:09.394469+00:00
-- url     : https://prove2.me/submissions/6d7a5a3b-7e73-44cb-acc3-de98db10a4c8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_RhGradStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ContinuousInvLeadingBlockEntry
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExF_cd_nM
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExF_unipotentFrame_inv_eq_adjugate
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_continuous
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_continuous


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
open GlobalTheory GlobalTheory.SharpGradient
open Filter Matrix
open scoped ComplexOrder ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.SharpGradient
theorem _root_.solution {r : ℕ} (X : Data E r) (τ : X.Ψ) (a b : Fin X.p0) :
    Continuous fun z : V (nd X) => (ExF.n1 X z τ)⁻¹ a b := by
  simp only [ExF.unipotentFrame_inv_eq_adjugate]
  have h : Continuous fun z : V (nd X) => ExF.n1 X z τ :=
    continuous_pi fun i => continuous_pi fun j => (ExF.cd_nM X τ _ _).continuous
  exact h.matrix_adjugate.matrix_elem a b
end GlobalTheory.SharpGradient
