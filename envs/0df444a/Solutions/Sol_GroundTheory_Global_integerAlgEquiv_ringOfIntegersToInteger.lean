-- Prove2me | solution 1 for GroundTheory.Global.integerAlgEquiv_ringOfIntegersToInteger
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:05:14.051872+00:00
-- url     : https://prove2.me/submissions/4c3b23f5-6cf0-4c67-b99b-f167a8cc0b90

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace_Galois
import Definitions.Def_GroundTheory_LocalFields_Ramification
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace_Inertia

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField ValuativeRel
  GroundTheory.LocalField
open scoped WithZero Pointwise
open GroundTheory GroundTheory.Global
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
  [Algebra (v.adicCompletion K) (w.adicCompletion L)]
  [ContinuousSMul (v.adicCompletion K) (w.adicCompletion L)]
  [IsScalarTower K (v.adicCompletion K) (w.adicCompletion L)]
namespace GroundTheory.Global
theorem _root_.solution (σ : MulAction.stabilizer Gal(L/K) w.asIdeal)
    (r : 𝓞 L) :
    integerAlgEquiv (v.adicCompletion K) (w.adicCompletion L) (decompositionToLocal v w σ)
        (ringOfIntegersToInteger w r) = ringOfIntegersToInteger w ((σ : Gal(L/K)) • r) := by
  apply Subtype.ext
  rw [coe_integerAlgEquiv_apply, coe_ringOfIntegersToInteger, coe_ringOfIntegersToInteger,
    decompositionToLocal_algebraMap]
  rfl
end GroundTheory.Global
