-- Prove2me | solution 1 for GroundTheory.Global.valued_of_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:59:36.434+00:00
-- url     : https://prove2.me/submissions/9bd5824b-4129-4b81-af4d-301892acc76b

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
variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K] (v : HeightOneSpectrum R)
namespace GroundTheory.Global
theorem _root_.solution {ϖ : v.adicCompletionIntegers K} (hϖ : Irreducible ϖ) :
    Valued.v (ϖ : v.adicCompletion K) = exp (-1 : ℤ) := by
  have h : Valuation.IsUniformizer (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)
      (ϖ : v.adicCompletion K) :=
    Valuation.isUniformizer_of_maximalIdeal_eq_span Valued.v
      ((IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ)
  rw [h.val, Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
    (valuedAdicCompletion_surjective K v)]
  rfl
end GroundTheory.Global
