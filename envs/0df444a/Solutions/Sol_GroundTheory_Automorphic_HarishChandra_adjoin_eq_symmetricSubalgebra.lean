-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.adjoin_eq_symmetricSubalgebra
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:08:03.166466+00:00
-- url     : https://prove2.me/submissions/e75a66ba-e250-4a38-9268-c714365b58bb

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Symmetric
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_symmetric_le_adjoin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.HarishChandra
open MvPolynomial Finset
variable {n : ℕ}
namespace GroundTheory.Automorphic.HarishChandra
theorem _root_.solution (q : Fin n → MvPolynomial (Fin n) ℂ)
    (hq : ∀ k, (q k).IsSymmetric)
    (hdeg : ∀ k, (q k - psum (Fin n) ℂ ((k : ℕ) + 1)).totalDegree < (k : ℕ) + 1) :
    Algebra.adjoin ℂ (Set.range q) = symmetricSubalgebra (Fin n) ℂ := by
  apply le_antisymm
  · exact Algebra.adjoin_le (by rintro _ ⟨k, rfl⟩; exact hq k)
  · intro p hp
    exact symmetric_le_adjoin q hq hdeg _ p hp le_rfl
end GroundTheory.Automorphic.HarishChandra
