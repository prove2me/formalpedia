-- Prove2me | solution 1 for GroundTheory.Global.finrank_integer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:08:45.407795+00:00
-- url     : https://prove2.me/submissions/1854bd86-801d-4ed5-8251-399e2a9e93ac

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace_Integers
import Theorems.Thm_GroundTheory_Global_isTorsionFree_integer_adicCompletion

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
open scoped WithZero
open GroundTheory GroundTheory.Global
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
  [Algebra (v.adicCompletion K) (w.adicCompletion L)]
  [ContinuousSMul (v.adicCompletion K) (w.adicCompletion L)]
  [IsScalarTower K (v.adicCompletion K) (w.adicCompletion L)]
namespace GroundTheory.Global
theorem _root_.solution :
    Module.finrank 𝒪[v.adicCompletion K] 𝒪[w.adicCompletion L] =
      Module.finrank (v.adicCompletion K) (w.adicCompletion L) :=
  have := isTorsionFree_integer_adicCompletion v w
  IsIntegralClosure.rank 𝒪[v.adicCompletion K] (v.adicCompletion K) (w.adicCompletion L) _
end GroundTheory.Global
