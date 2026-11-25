-- Prove2me | solution 1 for GroundTheory.Global.isUnramified_adicCompletion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:33:06.64504+00:00
-- url     : https://prove2.me/submissions/0b223669-92e3-4516-8c6d-e5ab7f2e6ff9

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_CycTate
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace_Galois
import Definitions.Def_GroundTheory_LocalFields_HerbrandLocal
import Definitions.Def_GroundTheory_LocalFields_UnramifiedNorms
import Definitions.Def_GroundTheory_LocalFields_HerbrandCyclic
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_LocalHerbrand
import Theorems.Thm_GroundTheory_Global_ramificationIdx_integer
import Theorems.Thm_GroundTheory_LocalField_isUnramified_iff


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
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField ValuativeRel GroundTheory.GroupCoh
open scoped Pointwise
open GroundTheory GroundTheory.Global
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
variable [Algebra (v.adicCompletion K) (w.adicCompletion L)]
  [ContinuousSMul (v.adicCompletion K) (w.adicCompletion L)]
  [IsScalarTower K (v.adicCompletion K) (w.adicCompletion L)]
omit [IsGalois K L]
namespace GroundTheory.Global
theorem _root_.solution (he : w.asIdeal.ramificationIdx (𝓞 K) = 1) :
    GroundTheory.LocalField.IsUnramified (v.adicCompletion K) (w.adicCompletion L) :=
  (GroundTheory.LocalField.isUnramified_iff _ _).2 (by
    rw [GroundTheory.LocalField.ramificationIndex, ramificationIdx_integer v w, he])
end GroundTheory.Global
