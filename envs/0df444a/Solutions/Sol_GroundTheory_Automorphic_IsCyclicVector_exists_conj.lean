-- Prove2me | solution 1 for GroundTheory.Automorphic.IsCyclicVector.exists_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:12:45.339417+00:00
-- url     : https://prove2.me/submissions/1fa9e7ad-a8ea-4ae7-b4b9-4e47e9080060

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_StableConjCyclic
import Theorems.Thm_GroundTheory_Automorphic_cyclicBasis_apply
import Theorems.Thm_GroundTheory_Automorphic_IsCyclicVector_exists_aeval_apply_eq
import Theorems.Thm_GroundTheory_Automorphic_aeval_apply_eq_sum_modByMonic

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
theorem _root_.solution {f' : Module.End E V'} {v' : V'} (hv : IsCyclicVector f v)
    (hv' : IsCyclicVector f' v') (hch : f.charpoly = f'.charpoly) :
    ∃ e : V ≃ₗ[E] V', ∀ x, e (f x) = f' (e x) := by
  have hdim : finrank E V = finrank E V' := by
    rw [← LinearMap.charpoly_natDegree f, ← LinearMap.charpoly_natDegree f', hch]
  let e : V ≃ₗ[E] V' := (cyclicBasis hv).equiv (cyclicBasis hv') (finCongr hdim)
  have he : ∀ k : Fin (finrank E V), e ((f ^ (k : ℕ)) v) = (f' ^ (k : ℕ)) v' := by
    intro k
    rw [← cyclicBasis_apply hv, Basis.equiv_apply, cyclicBasis_apply]
    rfl
  have hp : ∀ p : E[X], e (aeval f p v) = aeval f' p v' := by
    intro p
    rw [aeval_apply_eq_sum_modByMonic, aeval_apply_eq_sum_modByMonic, map_sum, ← hch]
    rw [← (finCongr hdim).sum_comp]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, he]
    rfl
  refine ⟨e, fun x => ?_⟩
  obtain ⟨p, rfl⟩ := hv.exists_aeval_apply_eq x
  have h1 : f (aeval f p v) = aeval f (X * p) v := by
    rw [map_mul, aeval_X, Module.End.mul_apply]
  rw [h1, hp, hp, map_mul, aeval_X, Module.End.mul_apply]
end IsCyclicVector
end GroundTheory.Automorphic
