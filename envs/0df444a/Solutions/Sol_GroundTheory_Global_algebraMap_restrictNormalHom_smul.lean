-- Prove2me | solution 1 for GroundTheory.Global.algebraMap_restrictNormalHom_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:26:57.977064+00:00
-- url     : https://prove2.me/submissions/d9b1707a-2cd1-421d-b211-d9ccc9c58ea9

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
theorem _root_.solution (σ : Gal(L/K)) (x : 𝓞 F) :
    algebraMap (𝓞 F) (𝓞 L) (AlgEquiv.restrictNormalHom F σ • x) =
      σ • algebraMap (𝓞 F) (𝓞 L) x := by
  apply RingOfIntegers.coe_injective
  change algebraMap F L ((σ.restrictNormal F) (x : F)) = σ (algebraMap F L (x : F))
  exact AlgEquiv.restrictNormal_commutes σ F x
end GroundTheory.Global
