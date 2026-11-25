-- Prove2me | solution 1 for GroundTheory.Global.AdeleBaseChange.completionMap_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:28:03.1417+00:00
-- url     : https://prove2.me/submissions/a879c623-4968-463e-87e2-3983edc0a4d2

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_NormTrace
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace_Integers
import Definitions.Def_GroundTheory_GlobalFields_Adele_BaseChange_FiniteMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open IsDedekindDomain NumberField TensorProduct Module Filter Topology
open scoped RestrictedProduct
noncomputable section
open GroundTheory.Global.AdeleBaseChange
open SemiLocal
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
namespace GroundTheory.Global.AdeleBaseChange
theorem _root_.solution {v v' : HeightOneSpectrum (𝓞 K)} (h : v = v')
    (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal] [w.asIdeal.LiesOver v'.asIdeal]
    (a : FiniteAdeleRing (𝓞 K) K) :
    completionMap v w (a v) = completionMap v' w (a v') := by
  subst h
  rfl
end GroundTheory.Global.AdeleBaseChange
