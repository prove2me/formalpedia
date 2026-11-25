-- Prove2me | solution 1 for GroundTheory.Automorphic.IsCyclicVector.exists_eq_aeval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:12:46.005378+00:00
-- url     : https://prove2.me/submissions/9fbee2c6-175d-40f4-90cc-036d56b1c366

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_StableConjCyclic
import Theorems.Thm_GroundTheory_Automorphic_cyclicBasis_apply
import Theorems.Thm_GroundTheory_Automorphic_IsCyclicVector_exists_aeval_apply_eq

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
namespace IsCyclicVector
theorem _root_.solution (hv : IsCyclicVector f v) {g : Module.End E V}
    (hg : Commute f g) : ∃ p : E[X], g = aeval f p := by
  obtain ⟨p, hp⟩ := hv.exists_aeval_apply_eq (g v)
  refine ⟨p, (cyclicBasis hv).ext fun k => ?_⟩
  rw [cyclicBasis_apply, ← Module.End.mul_apply, ← ((hg.pow_left (k : ℕ)).eq), Module.End.mul_apply,
    ← hp, ← Module.End.mul_apply, ← Module.End.mul_apply, ← aeval_X_pow (R := E) f, ← map_mul,
    ← map_mul, mul_comm]
end IsCyclicVector
end GroundTheory.Automorphic
