-- Prove2me | solution 1 for GroundTheory.Global.cyclicHerbrand_eq_of_real_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:25:16.189463+00:00
-- url     : https://prove2.me/submissions/21d83eaf-4b32-401b-af65-1f4a63313e41

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Cyclic
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_RationalForm
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Lattice
import Theorems.Thm_GroundTheory_Global_finite_quotient_of_smul_mem
import Theorems.Thm_GroundTheory_Global_cyclicHerbrand_eq_of_injective
import Theorems.Thm_GroundTheory_Global_exists_injective_intertwiner_of_real_equiv

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
open scoped TensorProduct
variable {G M M' : Type*} [Group G] [AddCommGroup M] [AddCommGroup M']
variable [Module.Finite ℤ M] [Module.Free ℤ M] [Module.Finite ℤ M'] [Module.Free ℤ M']
namespace GroundTheory.Global
theorem _root_.solution [Fintype G] (ρ : Representation ℤ G M)
    (ρ' : Representation ℤ G M') (σ : G) (e : ℝ ⊗[ℤ] M ≃ₗ[ℝ] ℝ ⊗[ℤ] M')
    (he : ∀ g x, e ((ρ g).baseChange ℝ x) = (ρ' g).baseChange ℝ (e x)) :
    cyclicHerbrand ρ σ = cyclicHerbrand ρ' σ := by
  obtain ⟨φ, hφ, ⟨n, hn, hrange⟩, hcomm⟩ := exists_injective_intertwiner_of_real_equiv ρ ρ' e he
  have : Finite (M' ⧸ φ.toAddMonoidHom.range) :=
    finite_quotient_of_smul_mem _ hn fun y => by
      obtain ⟨x, hx⟩ := hrange y
      exact ⟨x, hx⟩
  exact cyclicHerbrand_eq_of_injective ρ ρ' σ φ.toAddMonoidHom hφ hcomm
end GroundTheory.Global
