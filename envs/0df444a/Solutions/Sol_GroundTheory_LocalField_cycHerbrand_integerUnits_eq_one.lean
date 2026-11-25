-- Prove2me | solution 1 for GroundTheory.LocalField.cycHerbrand_integerUnits_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:08:25.818424+00:00
-- url     : https://prove2.me/submissions/9994087c-581b-4c1e-87bb-0050656d0b55

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_HerbrandLocalBase
import Definitions.Def_GroundTheory_LocalFields_CompleteTrivialLocal
import Definitions.Def_GroundTheory_LocalFields_HerbrandLocal
import Theorems.Thm_GroundTheory_LocalField_finiteIndex_of_isOpen_integerUnits
import Theorems.Thm_GroundTheory_LocalField_cycHerbrand_integerUnits_eq_one_of_subgroup
import Theorems.Thm_GroundTheory_LocalField_exists_openSubgroup_units_tateTrivial


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField
open ValuativeRel GroundTheory.GroupCoh GroundTheory.Global
variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
variable [IsGalois K L] {σ : L ≃ₐ[K] L}
namespace GroundTheory.LocalField
theorem _root_.solution (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    HasHerbrandQuotient
        (cycSubOne (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) 𝒪[L]ˣ) σ)
        (cycNorm (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) 𝒪[L]ˣ)) ∧
      cycHerbrand (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) 𝒪[L]ˣ) σ = 1 := by
  obtain ⟨-, -, -, -, -, -, -, V, hV, -, hopen, hT⟩ :=
    exists_openSubgroup_units_tateTrivial (K := K) (L := L)
  let := stableUnitsAction V hV
  have := finiteIndex_of_isOpen_integerUnits hopen
  have := hT.1
  have := hT.2
  exact cycHerbrand_integerUnits_eq_one_of_subgroup hσ V
    fun g v => Units.ext (Subtype.ext (unitVal_smul V hV g v))
end GroundTheory.LocalField
