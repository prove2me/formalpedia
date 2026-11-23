-- Prove2me | solution 1 for GroundTheory.Global.under_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:59:36.298804+00:00
-- url     : https://prove2.me/submissions/9425a6ba-a63c-4e26-86f8-48b6ef189db5

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
theorem _root_.solution (σ : Gal(L/K)) (Q : Ideal (𝓞 L)) :
    (σ • Q).under (𝓞 F) = AlgEquiv.restrictNormalHom F σ • Q.under (𝓞 F) := by
  ext x
  simp only [Ideal.mem_pointwise_smul_iff_inv_smul_mem, Ideal.under_def, Ideal.mem_comap,
    ← map_inv, algebraMap_restrictNormalHom_smul]
end GroundTheory.Global
