-- Prove2me | solution 1 for GroundTheory.Global.restrictNormalHom_mem_inertia
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:09:57.368113+00:00
-- url     : https://prove2.me/submissions/153d7cad-4a12-4084-ae49-0f4255281ace

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
omit [NumberField K] [NumberField F] [NumberField L] [IsGalois K L]
namespace GroundTheory.Global
theorem _root_.solution {Q : Ideal (𝓞 L)} {σ : Gal(L/K)}
    (hσ : σ ∈ Q.inertia Gal(L/K)) :
    AlgEquiv.restrictNormalHom F σ ∈ (Q.under (𝓞 F)).inertia Gal(F/K) := by
  rw [AddSubgroup.mem_inertia] at hσ ⊢
  intro x
  change algebraMap (𝓞 F) (𝓞 L) (AlgEquiv.restrictNormalHom F σ • x - x) ∈ Q
  rw [map_sub, algebraMap_restrictNormalHom_smul]
  exact hσ _
end GroundTheory.Global
