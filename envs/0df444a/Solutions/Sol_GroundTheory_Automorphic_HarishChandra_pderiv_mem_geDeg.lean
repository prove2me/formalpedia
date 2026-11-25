-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.pderiv_mem_geDeg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:56:54.089653+00:00
-- url     : https://prove2.me/submissions/f776aac3-9ce7-45ba-9087-831e6c9e915f

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemCenterOfCommuteE
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_RepBase
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_RhoOneEqZeroOfRhoZeroEqZero
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_map_mem_of_monomial
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_pderiv_monomial_mem_geDeg

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
theorem _root_.solution {t : ℕ} (a : Fin n × Fin n) {f : Poly n} (hf : f ∈ geDeg t) :
    pderiv a f ∈ geDeg (t - 1) := by
  refine map_mem_of_monomial (pderiv a : Derivation ℂ (Poly n) (Poly n)).toLinearMap _
    (fun s => t ≤ s.degree) (fun s hs => ?_) (fun s c hs => pderiv_monomial_mem_geDeg a s c hs)
  by_contra hlt
  exact hs (hf s (not_le.1 hlt))
end GroundTheory.Automorphic.HarishChandra
