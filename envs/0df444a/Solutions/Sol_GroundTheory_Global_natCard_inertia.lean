-- Prove2me | solution 1 for GroundTheory.Global.natCard_inertia
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:28:10.89484+00:00
-- url     : https://prove2.me/submissions/7ad8e0f7-4ffc-4290-b5bb-4a61ce3b0f51

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
  [IsGalois K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
  [Algebra (v.adicCompletion K) (w.adicCompletion L)]
  [ContinuousSMul (v.adicCompletion K) (w.adicCompletion L)]
  [IsScalarTower K (v.adicCompletion K) (w.adicCompletion L)]
omit [Algebra (v.adicCompletion K) (w.adicCompletion L)]
  [ContinuousSMul (v.adicCompletion K) (w.adicCompletion L)]
  [IsScalarTower K (v.adicCompletion K) (w.adicCompletion L)]
include v
namespace GroundTheory.Global
theorem _root_.solution :
    Nat.card (w.asIdeal.inertia Gal(L/K)) = w.asIdeal.ramificationIdx (𝓞 K) := by
  rw [Ideal.card_inertia_eq_ramificationIdxIn (G := Gal(L/K)) v.asIdeal w.asIdeal,
    Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal w.asIdeal Gal(L/K)]
end GroundTheory.Global
