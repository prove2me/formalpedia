-- Prove2me | solution 1 for GroundTheory.Global.Artin.subfieldPlaceEquiv_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:31:19.061644+00:00
-- url     : https://prove2.me/submissions/2492975e-f0ff-429d-bdb4-9bf274c8e925

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Artin_MackeyFrobeniusEmbed
import Definitions.Def_GroundTheory_GlobalFields_Artin_MemInvariantsCompSubtypeIff
import Definitions.Def_GroundTheory_GlobalFields_Artin_Places

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open scoped Pointwise
open NumberField IsDedekindDomain IntermediateField
open GroundTheory GroundTheory.Global GroundTheory.Global.Artin
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] (H : Subgroup Gal(L/K)) (v : HeightOneSpectrum (𝓞 K))
  (w : HeightOneSpectrum (𝓞 L))
namespace GroundTheory.Global.Artin
theorem _root_.solution [w.asIdeal.LiesOver v.asIdeal] (x : Gal(L/K)) :
    (subfieldPlaceEquiv H v w (DoubleCoset.mk _ _ x) : HeightOneSpectrum (𝓞 (fixedField H))) =
      subfieldPlace H w x :=
  rfl
end GroundTheory.Global.Artin
