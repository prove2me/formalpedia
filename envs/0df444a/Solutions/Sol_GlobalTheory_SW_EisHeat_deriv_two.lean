-- Prove2me | solution 1 for GlobalTheory.SW.EisHeat.deriv_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:35:36.908587+00:00
-- url     : https://prove2.me/submissions/990ad046-2037-47ca-93e2-5808ce8417bf

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
import Theorems.Thm_GlobalTheory_SW_EisHeat_deriv_line
import Theorems.Thm_GlobalTheory_SCV_analyticAt_of_differentiableOn
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
variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X] [FiniteDimensional ℂ X]
namespace GlobalTheory.SW.EisHeat
theorem _root_.solution {f : X → ℂ} {U : Set X} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) {p : X}
    (hp : p ∈ U) (v w : X) :
    deriv (fun s : ℂ => deriv (fun t : ℂ => f (p + s • v + t • w)) 0) 0 =
      fderiv ℂ (fderiv ℂ f) p v w := by
  have h1 : DifferentiableAt ℂ (fderiv ℂ f) p :=
    (SCV.analyticAt_of_differentiableOn hf (hU.mem_nhds hp)).fderiv.differentiableAt
  have h2 := (deriv_line h1 v).clm_apply (hasDerivAt_const (0 : ℂ) w)
  have h3 : ∀ᶠ s : ℂ in 𝓝 0, p + s • v ∈ U := by
    have : Continuous fun s : ℂ => p + s • v := by fun_prop
    exact this.continuousAt.eventually_mem (by simpa using hU.mem_nhds hp)
  have h4 : (fun s : ℂ => deriv (fun t : ℂ => f (p + s • v + t • w)) 0) =ᶠ[𝓝 0]
      fun s => fderiv ℂ f (p + s • v) w :=
    h3.mono fun s hs => (deriv_line (hf.differentiableAt (hU.mem_nhds hs)) w).deriv
  rw [h4.deriv_eq, h2.deriv]
  simp
end GlobalTheory.SW.EisHeat
