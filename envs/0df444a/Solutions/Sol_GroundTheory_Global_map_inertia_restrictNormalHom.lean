-- Prove2me | solution 1 for GroundTheory.Global.map_inertia_restrictNormalHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:46:32.042045+00:00
-- url     : https://prove2.me/submissions/f738da74-bce9-4542-a8b6-c2f1647b7ff8

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Artin_MemInvariantsCompSubtypeIff
import Definitions.Def_GroundTheory_GlobalFields_Artin_InflationTower
import Theorems.Thm_GroundTheory_Global_restrictNormalHom_mem_inertia
import Theorems.Thm_GroundTheory_Global_exists_mem_inertia_restrictNormalHom_eq

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
theorem _root_.solution (Q : Ideal (𝓞 L)) [Q.IsPrime] :
    (Q.inertia Gal(L/K)).map (AlgEquiv.restrictNormalHom F) =
      (Q.under (𝓞 F)).inertia Gal(F/K) := by
  ext τ
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    exact restrictNormalHom_mem_inertia hσ
  · intro hτ
    obtain ⟨σ, hσ, h⟩ := exists_mem_inertia_restrictNormalHom_eq Q hτ
    exact ⟨σ, hσ, h⟩
end GroundTheory.Global
