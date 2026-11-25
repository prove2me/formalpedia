-- Prove2me | solution 1 for GroundTheory.Global.placeBelow_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:32:32.682617+00:00
-- url     : https://prove2.me/submissions/9d7350db-b4f0-4f67-8f9b-546b5e21f79a

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Permutation
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_LatticeBridge
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Galois
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_SUnitsPerm
import Theorems.Thm_GroundTheory_Global_eq_placeBelow_of_liesOver

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
open MulAction NumberField IsDedekindDomain
open scoped Pointwise
noncomputable section
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]
omit [NumberField K] [NumberField L] [IsGalois K L]
namespace GroundTheory.Global
theorem _root_.solution (g : L ≃ₐ[K] L) (w : HeightOneSpectrum (𝓞 L)) :
    placeBelow (K := K) (g • w) = placeBelow w := by
  symm
  apply eq_placeBelow_of_liesOver
  change ((g • w.asIdeal : Ideal (𝓞 L))).LiesOver _
  infer_instance
end GroundTheory.Global
