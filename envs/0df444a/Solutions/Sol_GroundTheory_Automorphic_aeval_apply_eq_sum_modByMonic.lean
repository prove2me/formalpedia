-- Prove2me | solution 1 for GroundTheory.Automorphic.aeval_apply_eq_sum_modByMonic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:02:11.893264+00:00
-- url     : https://prove2.me/submissions/caeebd63-ec39-4821-8a62-c6770230ae3f

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_StableConjCyclic

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
theorem _root_.solution (f : Module.End E V) (v : V) (p : E[X]) :
    aeval f p v = ∑ k : Fin (finrank E V), (p %ₘ f.charpoly).coeff k • (f ^ (k : ℕ)) v := by
  have hmon := LinearMap.charpoly_monic f
  conv_lhs => rw [← modByMonic_add_div p f.charpoly]
  rw [map_add, map_mul, LinearMap.aeval_self_charpoly, zero_mul, add_zero]
  by_cases h0 : p %ₘ f.charpoly = 0
  · simp [h0]
  have hdeg : (p %ₘ f.charpoly).natDegree < finrank E V := by
    rw [Polynomial.natDegree_lt_iff_degree_lt h0, ← LinearMap.charpoly_natDegree f,
      ← degree_eq_natDegree hmon.ne_zero]
    exact degree_modByMonic_lt p hmon
  rw [aeval_eq_sum_range' hdeg, LinearMap.sum_apply,
    Finset.sum_range (fun i => ((p %ₘ f.charpoly).coeff i • f ^ i) v)]
  rfl
end GroundTheory.Automorphic
