-- Prove2me | solution 1 for GroundTheory.Global.IdeleNorm.map_integerUnitsOver_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:32:42.603786+00:00
-- url     : https://prove2.me/submissions/d0fa3199-66ca-4e91-aae4-db9b81041e91

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_LocalNorms
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_Splitting
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeRangeNormUnits
import Definitions.Def_GroundTheory_LocalFields_UnramifiedNorms
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace_Integers
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_LocalNormGroups
import Theorems.Thm_GroundTheory_Global_IdeleNorm_finiteLocalNorm_mem_integers

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
theorem _root_.solution (v : HeightOneSpectrum (𝓞 K)) :
    (integerUnitsOver L v).map (finiteLocalNorm L v) ≤
      (Submonoid.ofClass (v.adicCompletionIntegers K)).units := by
  rintro _ ⟨y, hy, rfl⟩
  refine (Submonoid.mem_units_iff _ _).2 ⟨finiteLocalNorm_mem_integers hy, ?_⟩
  rw [← map_inv]
  exact finiteLocalNorm_mem_integers (inv_mem hy)
end GroundTheory.Global.IdeleNorm
