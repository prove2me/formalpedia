-- Prove2me | solution 1 for GroundTheory.Global.IsArithFrobAt.restrictNormalHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:45:25.919364+00:00
-- url     : https://prove2.me/submissions/d4ee74a3-eb79-4bef-a99d-aec6b7ca49d9

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Artin_MemInvariantsCompSubtypeIff
import Definitions.Def_GroundTheory_GlobalFields_Artin_InflationTower
import Theorems.Thm_GroundTheory_Global_algebraMap_restrictNormalHom_smul

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
namespace GroundTheory.Global
namespace IsArithFrobAt
theorem _root_.solution {φ : Gal(L/K)} {Q : Ideal (𝓞 L)}
    (h : IsArithFrobAt (𝓞 K) φ Q) :
    IsArithFrobAt (𝓞 K) (AlgEquiv.restrictNormalHom F φ) (Q.under (𝓞 F)) := by
  intro x
  rw [Ideal.under_under]
  change algebraMap (𝓞 F) (𝓞 L) (AlgEquiv.restrictNormalHom F φ • x -
    x ^ Nat.card (𝓞 K ⧸ Q.under (𝓞 K))) ∈ Q
  rw [map_sub, map_pow, algebraMap_restrictNormalHom_smul]
  exact h _
end IsArithFrobAt
end GroundTheory.Global
