-- Prove2me | solution 1 for GroundTheory.Global.cycHerbrand_unitsRep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:15:43.737988+00:00
-- url     : https://prove2.me/submissions/8257596f-9bec-4be3-a798-fe7d623594a0

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_UnitsHerbrand
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_UnitsHerbrandValue
import Theorems.Thm_GroundTheory_Global_cycHerbrand_logLatticeRep_mul_card
import Theorems.Thm_GroundTheory_Global_cycHerbrand_funPermRep
import Theorems.Thm_GroundTheory_Global_cycHerbrand_unitsRep_eq_logLattice
import Theorems.Thm_GroundTheory_Global_prod_card_stabilizer_infinitePlace


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
open NumberField NumberField.Units NumberField.InfinitePlace MulAction Module
open scoped TensorProduct
noncomputable section
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable [IsGalois K L]
open scoped Classical
namespace GroundTheory.Global
theorem _root_.solution {σ : L ≃ₐ[K] L} (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    cycHerbrand (unitsRep K L) σ =
      (∏ v : InfinitePlace K, (if v.IsUnramifiedIn L then 1 else 2 : ℚ)) / finrank K L := by
  have h1 := cycHerbrand_logLatticeRep_mul_card hσ
  rw [cycHerbrand_funPermRep hσ, prod_card_stabilizer_infinitePlace] at h1
  have h2 : (Fintype.card (L ≃ₐ[K] L) : ℚ) = finrank K L := by
    rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]
  have h3 : (finrank K L : ℚ) ≠ 0 := by
    exact_mod_cast Module.finrank_pos.ne'
  rw [cycHerbrand_unitsRep_eq_logLattice hσ, eq_div_iff h3, ← h2, h1]
end GroundTheory.Global
