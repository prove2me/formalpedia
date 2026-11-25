-- Prove2me | solution 1 for GroundTheory.LocalField.cycHerbrand_eq_one_of_subsingleton
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:41:54.854235+00:00
-- url     : https://prove2.me/submissions/3a29d8fa-a64e-43c7-85e6-5214ebdcbc1b

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_CycTate
import Definitions.Def_GroundTheory_LocalFields_CompleteTrivial
import Definitions.Def_GroundTheory_LocalFields_HerbrandCyclic
import Theorems.Thm_GroundTheory_LocalField_cycHerbrand_ofMulDistribMulAction
import Theorems.Thm_GroundTheory_LocalField_hasHerbrandQuotient_iff

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
open GroundTheory.GroupCoh GroundTheory.Global
variable {G M : Type*} [Group G] [Fintype G] [CommGroup M] [MulDistribMulAction G M]
variable {σ : G}
namespace GroundTheory.LocalField
theorem _root_.solution (hσ : ∀ g, g ∈ Subgroup.zpowers σ)
    [Subsingleton (TateZero G M)] [Subsingleton (TateNegOne G M)] :
    HasHerbrandQuotient (cycSubOne (Representation.ofMulDistribMulAction G M) σ)
        (cycNorm (Representation.ofMulDistribMulAction G M)) ∧
      cycHerbrand (Representation.ofMulDistribMulAction G M) σ = 1 := by
  refine ⟨(hasHerbrandQuotient_iff hσ).mpr ⟨inferInstance, inferInstance⟩, ?_⟩
  rw [cycHerbrand_ofMulDistribMulAction hσ, Nat.card_unique, Nat.card_unique]
  norm_num
end GroundTheory.LocalField
