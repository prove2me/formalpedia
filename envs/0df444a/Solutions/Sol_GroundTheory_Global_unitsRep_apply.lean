-- Prove2me | solution 1 for GroundTheory.Global.unitsRep_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:32:59.042822+00:00
-- url     : https://prove2.me/submissions/bc5fc304-58b6-491a-bbd0-c972fc198635

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SUnits
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Galois
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_SUnitsPerm
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_SUnitsRep

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
open NumberField IsDedekindDomain NumberField.Units
open scoped Pointwise
noncomputable section
variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable [NumberField L]
omit [NumberField L]
namespace GroundTheory.Global
theorem _root_.solution (g : L ≃ₐ[K] L) (u : Additive (𝓞 L)ˣ) :
    unitsRep K L g u = Additive.ofMul (unitsMap g u.toMul) :=
  rfl
end GroundTheory.Global
