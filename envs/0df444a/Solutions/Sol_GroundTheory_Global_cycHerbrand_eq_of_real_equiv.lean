-- Prove2me | solution 1 for GroundTheory.Global.cycHerbrand_eq_of_real_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:37:52.16751+00:00
-- url     : https://prove2.me/submissions/ca11fdf5-a7d6-4f02-a080-d751f005abe1

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Cyclic
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Lattice
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Permutation
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_CycTate
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_LatticeBridge
import Theorems.Thm_GroundTheory_Global_cyclicHerbrand_eq_of_real_equiv


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
open MulAction
open scoped TensorProduct
variable {G : Type*} [Group G] [Fintype G]
namespace GroundTheory.Global
theorem _root_.solution {M M' : Type*} [AddCommGroup M] [Module.Finite ℤ M]
    [Module.Free ℤ M] [AddCommGroup M'] [Module.Finite ℤ M'] [Module.Free ℤ M']
    (ρ : Representation ℤ G M) (ρ' : Representation ℤ G M') (σ : G)
    (e : ℝ ⊗[ℤ] M ≃ₗ[ℝ] ℝ ⊗[ℤ] M')
    (he : ∀ g x, e ((ρ g).baseChange ℝ x) = (ρ' g).baseChange ℝ (e x)) :
    cycHerbrand ρ σ = cycHerbrand ρ' σ :=
  cyclicHerbrand_eq_of_real_equiv ρ ρ' σ e he
end GroundTheory.Global
