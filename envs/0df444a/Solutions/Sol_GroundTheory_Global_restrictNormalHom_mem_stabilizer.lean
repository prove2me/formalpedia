-- Prove2me | solution 1 for GroundTheory.Global.restrictNormalHom_mem_stabilizer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:09:48.207998+00:00
-- url     : https://prove2.me/submissions/ba8ab6ef-85c1-4413-a2fc-21e98c0e1175

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Artin_MemInvariantsCompSubtypeIff
import Definitions.Def_GroundTheory_GlobalFields_Artin_InflationTower
import Theorems.Thm_GroundTheory_Global_under_smul

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
    (hσ : σ ∈ MulAction.stabilizer Gal(L/K) Q) :
    AlgEquiv.restrictNormalHom F σ ∈ MulAction.stabilizer Gal(F/K) (Q.under (𝓞 F)) := by
  rw [MulAction.mem_stabilizer_iff] at hσ ⊢
  rw [← under_smul, hσ]
end GroundTheory.Global
