-- Prove2me | solution 1 for GlobalTheory.GaloisDescent.mem_range_of_repr_mem_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:08:43.694351+00:00
-- url     : https://prove2.me/submissions/7433c36a-ed81-4e5b-9fb0-93a77085592d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsOneTmulOfForallFixed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Module
open GlobalTheory GlobalTheory.GaloisDescent
variable {K L V M G : Type*} [Field K] [Field L] [Algebra K L] [AddCommGroup V] [Module K V]
  [AddCommGroup M] [Module K M] [Module L M] [IsScalarTower K L M] {f : V →ₗ[K] M}
namespace GlobalTheory.GaloisDescent
theorem _root_.solution (hf : IsBaseChange L f) {ι : Type*} (b : Basis ι K V) (u : M)
    (hu : ∀ i, (hf.basis b).repr u i ∈ Set.range (algebraMap K L)) : u ∈ LinearMap.range f := by
  classical
  choose k hk using hu
  rw [← (hf.basis b).linearCombination_repr u, Finsupp.linearCombination_apply, Finsupp.sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [← hk, algebraMap_smul, hf.basis_apply]
  exact Submodule.smul_mem _ _ ⟨_, rfl⟩
end GlobalTheory.GaloisDescent
