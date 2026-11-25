-- Prove2me | solution 1 for GroundTheory.Global.algebraMap_adicCompletion_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:08:04.78285+00:00
-- url     : https://prove2.me/submissions/26862982-ec55-40fa-b653-ade6dc9ac67e

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_LocalFieldAtPlace
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace
import Theorems.Thm_GroundTheory_Global_residueFieldEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.residueFieldEquiv_mk



set_option autoImplicit false
noncomputable section
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped WithZero
open GroundTheory GroundTheory.Global
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [Algebra (v.adicCompletion K) (w.adicCompletion L)]
  [ContinuousSMul (v.adicCompletion K) (w.adicCompletion L)]
  [IsScalarTower K (v.adicCompletion K) (w.adicCompletion L)]
namespace GroundTheory.Global
theorem _root_.solution [w.asIdeal.LiesOver v.asIdeal] :
    algebraMap (v.adicCompletion K) (w.adicCompletion L) = adicCompletionMap v w := by
  have h := (denseRange_algebraMap (R := 𝓞 K) (K := K) v).equalizer
    (continuous_algebraMap (v.adicCompletion K) (w.adicCompletion L))
    (continuous_adicCompletionMap v w) (funext fun x ↦ ?_)
  · exact RingHom.ext (congrFun h)
  · simp only [Function.comp_apply]
    rw [adicCompletionMap_algebraMap, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply K L (w.adicCompletion L)]
end GroundTheory.Global
