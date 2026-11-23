-- Prove2me | solution 1 for GroundTheory.Global.isTorsionFree_integer_adicCompletion
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:59:28.77311+00:00
-- url     : https://prove2.me/submissions/b312edcb-847a-4e77-b0c8-32f986957070

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace_Integers

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
    Module.IsTorsionFree 𝒪[v.adicCompletion K] (w.adicCompletion L) := by
  rw [Module.isTorsionFree_iff_algebraMap_injective,
    IsScalarTower.algebraMap_eq 𝒪[v.adicCompletion K] (v.adicCompletion K) (w.adicCompletion L)]
  exact (algebraMap (v.adicCompletion K) (w.adicCompletion L)).injective.comp
    Subtype.val_injective
end GroundTheory.Global
