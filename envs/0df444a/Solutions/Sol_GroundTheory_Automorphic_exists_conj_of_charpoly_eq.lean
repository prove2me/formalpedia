-- Prove2me | solution 1 for GroundTheory.Automorphic.exists_conj_of_charpoly_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:45:08.974478+00:00
-- url     : https://prove2.me/submissions/03d52c4a-0675-4279-bf6d-7c479aa0c495

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_StableConjCyclic
import Theorems.Thm_GroundTheory_Automorphic_exists_isCyclicVector
import Theorems.Thm_GroundTheory_Automorphic_IsCyclicVector_exists_conj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open Polynomial Module Matrix
variable {E V V' : Type*} [Field E] [AddCommGroup V] [Module E V] [FiniteDimensional E V]
  [AddCommGroup V'] [Module E V'] [FiniteDimensional E V']
variable {f : Module.End E V} {v : V}
namespace GroundTheory.Automorphic
theorem _root_.solution [Infinite E] {f f' : Module.End E V}
    (hf : f.charpoly.Separable) (hch : f.charpoly = f'.charpoly) :
    ∃ e : V ≃ₗ[E] V, ∀ x, e (f x) = f' (e x) := by
  obtain ⟨v, hv⟩ := exists_isCyclicVector f hf
  obtain ⟨v', hv'⟩ := exists_isCyclicVector f' (hch ▸ hf)
  exact hv.exists_conj hv' hch
end GroundTheory.Automorphic
