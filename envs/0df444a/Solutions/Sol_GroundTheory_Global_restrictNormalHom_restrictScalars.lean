-- Prove2me | solution 1 for GroundTheory.Global.restrictNormalHom_restrictScalars
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:59:35.64906+00:00
-- url     : https://prove2.me/submissions/6253221c-54c0-4406-b341-54705efc11c6

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
omit [NumberField K] [NumberField F] [NumberField L] [IsGalois K L]
namespace GroundTheory.Global
theorem _root_.solution (g : Gal(L/F)) :
    AlgEquiv.restrictNormalHom F (g.restrictScalars K) = 1 := by
  refine AlgEquiv.ext fun x => (algebraMap F L).injective ?_
  change algebraMap F L (((g.restrictScalars K).restrictNormal F) x) = algebraMap F L x
  rw [AlgEquiv.restrictNormal_commutes]
  exact g.commutes x
end GroundTheory.Global
