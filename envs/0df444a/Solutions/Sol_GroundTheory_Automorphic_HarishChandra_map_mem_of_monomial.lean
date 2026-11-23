-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.map_mem_of_monomial
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:17:05.973206+00:00
-- url     : https://prove2.me/submissions/f73cdc07-ecdd-46f0-99a8-c29d44c057ff

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemCenterOfCommuteE
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_RepBase
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_RhoOneEqZeroOfRhoZeroEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.HarishChandra
attribute [local instance 100] LieRing.ofAssociativeRing
open MvPolynomial
variable {n : ℕ}
namespace GroundTheory.Automorphic.HarishChandra
theorem _root_.solution (L : Poly n →ₗ[ℂ] Poly n) (P : Submodule ℂ (Poly n))
    (Q : (Fin n × Fin n →₀ ℕ) → Prop) {f : Poly n} (hf : ∀ s, coeff s f ≠ 0 → Q s)
    (h : ∀ s (c : ℂ), Q s → L (monomial s c) ∈ P) : L f ∈ P := by
  rw [f.as_sum, map_sum]
  exact Submodule.sum_mem _ fun s hs => h s _ (hf s (mem_support_iff.1 hs))
end GroundTheory.Automorphic.HarishChandra
