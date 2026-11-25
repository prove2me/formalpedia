-- Prove2me | solution 1 for GroundTheory.Global.decompositionMulEquiv_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:57:12.64254+00:00
-- url     : https://prove2.me/submissions/90bfdcb4-4d44-4e27-87ba-e4bb2a9ab7dd

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace_Degree
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace_Galois

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
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped WithZero Pointwise
open GroundTheory GroundTheory.Global
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
  [Algebra (v.adicCompletion K) (w.adicCompletion L)]
  [ContinuousSMul (v.adicCompletion K) (w.adicCompletion L)]
  [IsScalarTower K (v.adicCompletion K) (w.adicCompletion L)]
namespace GroundTheory.Global
theorem _root_.solution (σ : MulAction.stabilizer Gal(L/K) w.asIdeal) :
    decompositionMulEquiv v w σ = decompositionToLocal v w σ :=
  rfl
end GroundTheory.Global
