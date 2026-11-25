-- Prove2me | solution 1 for GroundTheory.Global.IdeleNorm.finiteLocalNorm_mem_integers
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:13:49.048578+00:00
-- url     : https://prove2.me/submissions/da941c90-e30f-4466-8391-63831a54fbf8

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_LocalNorms
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_Splitting
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeRangeNormUnits
import Definitions.Def_GroundTheory_LocalFields_UnramifiedNorms
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace_Integers
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_LocalNormGroups
import Theorems.Thm_GroundTheory_Global_IdeleNorm_coe_finiteLocalNorm
import Theorems.Thm_GroundTheory_Global_mem_valuationInteger_iff
import Theorems.Thm_GroundTheory_LocalField_norm_mem_integer


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
open IsDedekindDomain NumberField Filter Topology ValuativeRel
open AdeleBaseChange SemiLocal
open scoped NumberField.LiesOver TensorProduct
noncomputable section
open GroundTheory.Global.IdeleNorm
variable {K : Type*} [Field K] [NumberField K] {L : Type*} [Field L] [NumberField L] [Algebra K L]
namespace GroundTheory.Global.IdeleNorm
theorem _root_.solution {v : HeightOneSpectrum (𝓞 K)}
    {y : (w : PlacesOver L v) → (w.1.adicCompletion L)ˣ} (hy : y ∈ integerUnitsOver L v) :
    (finiteLocalNorm L v y : v.adicCompletion K) ∈ v.adicCompletionIntegers K := by
  rw [coe_finiteLocalNorm]
  refine prod_mem fun w _ ↦ ?_
  have h := (Submonoid.mem_units_iff _ _).1 (mem_integerUnitsOver.1 hy w)
  rw [← mem_valuationInteger_iff]
  exact LocalField.norm_mem_integer ((mem_valuationInteger_iff w.1 _).2 h.1)
end GroundTheory.Global.IdeleNorm
