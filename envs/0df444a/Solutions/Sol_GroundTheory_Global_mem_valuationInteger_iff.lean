-- Prove2me | solution 1 for GroundTheory.Global.mem_valuationInteger_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:40:17.223193+00:00
-- url     : https://prove2.me/submissions/e48e8210-4617-4279-a927-7980202d8de9

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_LocalAtPlace
import Definitions.Def_GroundTheory_GlobalFields_LocalFieldAtPlace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField WithZero
open scoped WithZero
open GroundTheory GroundTheory.Global
open ValuativeRel
variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K] (v : HeightOneSpectrum R)
namespace GroundTheory.Global
theorem _root_.solution (x : v.adicCompletion K) :
    x ∈ 𝒪[v.adicCompletion K] ↔ x ∈ v.adicCompletionIntegers K := by
  rw [Valuation.mem_integer_iff, mem_adicCompletionIntegers,
    (ValuativeRel.isEquiv (ValuativeRel.valuation (v.adicCompletion K)) Valued.v).le_one_iff_le_one]
end GroundTheory.Global
