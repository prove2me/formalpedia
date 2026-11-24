-- Prove2me | solution 1 for GlobalTheory.integrableOn_fundamentalDomain_of_continuous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:00:11.613671+00:00
-- url     : https://prove2.me/submissions/24b795d9-ba58-4fc7-86be-138941fc4639

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_TileIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IntegrableOnFundamentalDomainOfContinuous

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open MeasureTheory
variable {V κ : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [Fintype κ]
namespace GlobalTheory
theorem _root_.solution {E : Type} [NormedAddCommGroup E]
    (μ : Measure V) [μ.IsAddHaarMeasure] (b : Module.Basis κ ℝ V)
    (f : V → E) (hf : Continuous f) : IntegrableOn f (ZSpan.fundamentalDomain b) μ :=
  (hf.continuousOn.integrableOn_compact
    (ZSpan.fundamentalDomain_isBounded b).isCompact_closure).mono_set subset_closure
end GlobalTheory
