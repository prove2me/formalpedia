-- Prove2me | solution 1 for GroundTheory.Global.coe_integerUnitsAddEquiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T06:37:05.121989+00:00
-- url     : https://prove2.me/submissions/6a23a8f7-0c68-4c26-8b05-5d2e057e8c37

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_CycTate
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace_Galois
import Definitions.Def_GroundTheory_LocalFields_HerbrandLocal
import Definitions.Def_GroundTheory_LocalFields_UnramifiedNorms
import Definitions.Def_GroundTheory_LocalFields_HerbrandCyclic
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_LocalHerbrand

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
namespace GroundTheory.Global
theorem _root_.solution (x : Additive (w.adicCompletionIntegers L)ˣ) :
    ((((integerUnitsAddEquiv w x).toMul : 𝒪[w.adicCompletion L]ˣ) : 𝒪[w.adicCompletion L]) :
      w.adicCompletion L) = ((x.toMul : w.adicCompletionIntegers L) : w.adicCompletion L) :=
  rfl
end GroundTheory.Global
