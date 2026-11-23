-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.monomial_mem_geDeg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:13:48.312224+00:00
-- url     : https://prove2.me/submissions/f466a667-f40a-491c-8ca8-e3abe03e8d33

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
theorem _root_.solution {t : ℕ} (s : Fin n × Fin n →₀ ℕ) (c : ℂ) (h : t ≤ s.degree) :
    (monomial s c : Poly n) ∈ geDeg t := by
  intro s' hs'
  rw [coeff_monomial, if_neg]
  rintro rfl
  omega
end GroundTheory.Automorphic.HarishChandra
