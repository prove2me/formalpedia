-- Prove2me | solution 1 for GroundTheory.Global.map_stabilizer_restrictNormalHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:47:34.363618+00:00
-- url     : https://prove2.me/submissions/cd39b896-464a-4d83-84e9-48c29d9ff064

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Artin_MemInvariantsCompSubtypeIff
import Definitions.Def_GroundTheory_GlobalFields_Artin_InflationTower
import Theorems.Thm_GroundTheory_Global_restrictNormalHom_mem_stabilizer
import Theorems.Thm_GroundTheory_Global_exists_mem_stabilizer_restrictNormalHom_eq

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
omit [NumberField K]
namespace GroundTheory.Global
theorem _root_.solution (Q : Ideal (𝓞 L)) [Q.IsPrime] :
    (MulAction.stabilizer Gal(L/K) Q).map (AlgEquiv.restrictNormalHom F) =
      MulAction.stabilizer Gal(F/K) (Q.under (𝓞 F)) := by
  ext τ
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    exact restrictNormalHom_mem_stabilizer hσ
  · intro hτ
    obtain ⟨σ, hσ, h⟩ := exists_mem_stabilizer_restrictNormalHom_eq Q hτ
    exact ⟨σ, hσ, h⟩
end GroundTheory.Global
