-- Prove2me | solution 1 for GlobalTheory.SW.EisHeat.isHeat_tsum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:01:55.726278+00:00
-- url     : https://prove2.me/submissions/beaaa23b-a864-4b70-91ff-d6558cbbb687

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatInnerProductSelfNonnegBoundsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_PosSemidefSubMulConjTranspose
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianThetaEisensteinConvergeBoundedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EisAutomorphyLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_DerivDerivConstMulCexpBilinearAtZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustStatementPfA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EisensteinSeriesOfSchwartzIsHolomorphic
import Theorems.Thm_GlobalTheory_SW_EisHeat_isOpen_dom
import Theorems.Thm_GlobalTheory_SW_EisHeat_heat_iff
import Theorems.Thm_GlobalTheory_SCV_analyticAt_of_differentiableOn
import Theorems.Thm_GlobalTheory_SCV_differentiableOn_of_hasSumLocallyUniformlyOn
import Theorems.Thm_GlobalTheory_SCV_hasSumLocallyUniformlyOn_fderiv
import Theorems.Thm_GlobalTheory_SCV_hasSumLocallyUniformlyOn_of_locally_normal
import Theorems.Thm_GlobalTheory_SW_WeilAct_unique
import Theorems.Thm_GlobalTheory_SW_rowEmb_apply
import Theorems.Thm_GlobalTheory_spanCovol_bot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.SW.rowEmb_apply
attribute [local simp] GlobalTheory.spanCovol_bot



set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.EisHeat
variable {E : Type} [Field E] (Ψ : Finset (E →+* ℂ)) {n N : ℕ}
namespace GlobalTheory.SW.EisHeat
theorem _root_.solution {ι : Type} {D : ι → CM Ψ N N → CM Ψ n N → CM Ψ n N → ℂ}
    (hD : ∀ i, IsHeat Ψ (D i))
    (hle : ∀ p : CF Ψ N N × CF Ψ n N × CF Ψ n N, (p.1 : CM Ψ N N) ∈ Hn Ψ N → ∃ t ∈ 𝓝 p,
      ∃ u : ι → ℝ, Summable u ∧ ∀ i, ∀ q ∈ t, ‖D i q.1 q.2.1 q.2.2‖ ≤ u i) :
    IsHeat Ψ fun Z z z' => ∑' i, D i Z z z' := by
  have h0 := SCV.hasSumLocallyUniformlyOn_of_locally_normal
    (F := fun i (q : CF Ψ N N × CF Ψ n N × CF Ψ n N) => D i q.1 q.2.1 q.2.2)
    (U := {p | (p.1 : CM Ψ N N) ∈ Hn Ψ N}) hle
  have hd := SCV.differentiableOn_of_hasSumLocallyUniformlyOn (isOpen_dom Ψ) h0 fun i => (hD i).1
  have h1 := SCV.hasSumLocallyUniformlyOn_fderiv (isOpen_dom Ψ) h0 fun i => (hD i).1
  have h2 := SCV.hasSumLocallyUniformlyOn_fderiv (isOpen_dom Ψ) h1 fun i p hp =>
    (SCV.analyticAt_of_differentiableOn (hD i).1
      ((isOpen_dom Ψ).mem_nhds hp)).fderiv.differentiableAt.differentiableWithinAt
  refine (heat_iff Ψ hd).2 fun Z z z' hZ τ a b => ?_
  have hp : ((Z, z, z') : CF Ψ N N × CF Ψ n N × CF Ψ n N) ∈
    {p : CF Ψ N N × CF Ψ n N × CF Ψ n N | (p.1 : CM Ψ N N) ∈ Hn Ψ N} := hZ
  have s1 := fun v => (h1.hasSum hp).mapL (ContinuousLinearMap.apply ℂ ℂ v)
  have s2 := fun v w => ((h2.hasSum hp).mapL (ContinuousLinearMap.apply ℂ _ v)).mapL
    (ContinuousLinearMap.apply ℂ ℂ w)
  simp only [ContinuousLinearMap.apply_apply] at s1 s2
  refine ((s1 _).mul_left _).unique ?_
  simp only [fun i => (heat_iff Ψ (hD i).1).1 (hD i) Z z z' hZ τ a b]
  exact hasSum_sum fun k _ => s2 _ _
end GlobalTheory.SW.EisHeat
