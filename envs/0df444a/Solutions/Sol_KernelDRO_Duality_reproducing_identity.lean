-- Prove2me | solution 1 for KernelDRO.Duality.reproducing_identity
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T10:33:05.716403+00:00
-- url     : https://prove2.me/submissions/6a48f830-1447-4b71-b373-13870d23c283

import Mathlib
import Definitions.Def_WassersteinDRO_Duality_erealExpectation
import Definitions.Def_KernelDRO_Duality_Setting
set_option autoImplicit false
open MeasureTheory WassersteinDRO.Duality KernelDRO.Duality

theorem solution {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X]
    [BorelSpace X] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (φ : X → H) (hφ : Continuous φ) (f : H) (P : ProbabilityMeasure X) :
    ∫ ξ, rkhsEval φ f ξ ∂(P : Measure X) = inner ℝ f (meanEmbedding φ P) := by
  have hint : Integrable φ (P : Measure X) :=
    hφ.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace φ)
  exact integral_inner hint f
