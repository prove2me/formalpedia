-- Prove2me | solution 1 for GroundTheory.Global.restrictScalars_smul_ideal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:09:49.033848+00:00
-- url     : https://prove2.me/submissions/f9c56971-6d14-40a3-ac0d-9f59a7fc5ba4

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Artin_MemInvariantsCompSubtypeIff
import Definitions.Def_GroundTheory_GlobalFields_Artin_InflationTower

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
open IsDedekindDomain NumberField
open scoped Pointwise
open GroundTheory GroundTheory.Global
variable {K F L : Type*} [Field K] [NumberField K] [Field F] [NumberField F] [Field L]
  [NumberField L] [Algebra K F] [Algebra K L] [Algebra F L] [IsScalarTower K F L]
  [IsGalois K F] [IsGalois K L]
omit [NumberField K] [NumberField F] [NumberField L] [IsGalois K F] [IsGalois K L]
namespace GroundTheory.Global
theorem _root_.solution (g : Gal(L/F)) (I : Ideal (𝓞 L)) :
    g.restrictScalars K • I = g • I := by
  rw [Ideal.pointwise_smul_def, Ideal.pointwise_smul_def]
  rfl
end GroundTheory.Global
