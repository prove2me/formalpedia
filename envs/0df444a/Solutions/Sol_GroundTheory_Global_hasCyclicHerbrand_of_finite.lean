-- Prove2me | solution 1 for GroundTheory.Global.hasCyclicHerbrand_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:26:35.120715+00:00
-- url     : https://prove2.me/submissions/1ca78bca-a328-410f-be8f-fd8c0c516ae9

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CyclicSubtraction
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Cyclic
import Theorems.Thm_GroundTheory_Global_normHom_eq_card_smul
import Theorems.Thm_GroundTheory_Global_card_smul_sub_normHom_mem
import Theorems.Thm_GroundTheory_Global_finite_kerModRange_of_smul_mem

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
open GroundTheory.GroupCoh
variable {G M : Type*} [Group G] [Fintype G] [AddCommGroup M] [Module.Finite ℤ M]
namespace GroundTheory.Global
theorem _root_.solution (ρ : Representation ℤ G M) {σ : G}
    (hσ : ∀ g, g ∈ Subgroup.zpowers σ) : HasCyclicHerbrand ρ σ := by
  have hn : (Fintype.card G : ℤ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  refine ⟨finite_kerModRange_of_smul_mem _ _ hn fun x hx => ?_,
    finite_kerModRange_of_smul_mem _ _ hn fun x hx => ?_⟩
  · rw [← normHom_eq_card_smul ρ hσ hx]
    exact ⟨x, rfl⟩
  · have := card_smul_sub_normHom_mem ρ hσ x
    rwa [AddMonoidHom.mem_ker.1 hx, sub_zero] at this
end GroundTheory.Global
