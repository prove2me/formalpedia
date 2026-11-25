-- Prove2me | solution 1 for GroundTheory.Global.IdeleGroup.diagonal_unitsToUnits_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:03:56.686319+00:00
-- url     : https://prove2.me/submissions/287531c5-7e44-4bce-b1c2-63129f9b087b

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms
import Definitions.Def_GroundTheory_GlobalFields_Adele_Compact
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_UnitBound
import Theorems.Thm_GroundTheory_Global_IdeleGroup_mem_standardOpenSubgroup
import Theorems.Thm_GroundTheory_Global_coe_mem_adicCompletionIntegers_iff


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
open NumberField IsDedekindDomain Topology Filter NumberField.Units
  NumberField.Units.dirichletUnitTheorem
open scoped NumberField.AdeleRing RestrictedProduct
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
open GroundTheory.Global.IdeleGroup
namespace GroundTheory.Global.IdeleGroup
theorem _root_.solution (u : (𝓞 K)ˣ) :
    diagonal K (unitsToUnits K u) ∈ standardOpenSubgroup K := by
  rw [mem_standardOpenSubgroup K]
  intro v
  refine ⟨(coe_mem_adicCompletionIntegers_iff v _).2 (HeightOneSpectrum.valuation_le_one v _),
    ?_⟩
  rw [← map_inv]
  exact (coe_mem_adicCompletionIntegers_iff v _).2
    (HeightOneSpectrum.valuation_le_one v ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K))
end GroundTheory.Global.IdeleGroup
