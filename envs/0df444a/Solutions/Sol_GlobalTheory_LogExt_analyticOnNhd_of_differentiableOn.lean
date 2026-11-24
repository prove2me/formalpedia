-- Prove2me | solution 1 for GlobalTheory.LogExt.analyticOnNhd_of_differentiableOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:27:36.042656+00:00
-- url     : https://prove2.me/submissions/5bc35383-382f-4999-ac24-510cee05fac2

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FderivIntegralApplyOfHolomorphicOfDominated
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RiemannExtensionOfLogGrowth
import Theorems.Thm_GlobalTheory_SCV_analyticOnNhd_of_differentiableOn


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LogExt
open Filter Topology Asymptotics Metric Set Complex
open scoped Real
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
open Filter Topology Asymptotics Metric Set Complex
open scoped Real
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
namespace GlobalTheory.LogExt
namespace _root_.GlobalTheory.LogExt
theorem _root_.solution [FiniteDimensional ℂ V] {U : Set V}
    {f : V → ℂ} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) : AnalyticOnNhd ℂ f U :=
  _root_.GlobalTheory.SCV.analyticOnNhd_of_differentiableOn hU hf
end _root_.GlobalTheory.LogExt
end GlobalTheory.LogExt
