-- Prove2me | solution 1 for IharaTower.RungAssembly.map_delta_of_sq_sub
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/84c3e583-07b4-58fd-865a-b0d2d746d4e1

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IharaTower_RungAssembly_map_delta_of_sq_sub

set_option autoImplicit false

theorem solution {𝒪 : Type} [CommRing 𝒪] {T : Type} [CommRing T] [Algebra 𝒪 T]
    (πT : T →ₐ[𝒪] 𝒪) (a t Δ : T) (p nu nl nq n1 : ℕ)
    (hnu : nu = 1) (hnl : nl = 1) (hnq : nq = p + 1) (hn1 : n1 = p + 1)
    (hαq : a * a - t * a + algebraMap 𝒪 T (p : 𝒪) = 0)
    (hΔ : Δ = a ^ 2 * (algebraMap 𝒪 T (nu : 𝒪) * t) - a * (algebraMap 𝒪 T (nq : 𝒪) + algebraMap 𝒪 T (n1 : 𝒪))
        + algebraMap 𝒪 T (nl : 𝒪) * t) :
    πT Δ = (πT a - πT (t - a)) * (πT a ^ 2 - 1) := by
  subst hnu hnl hnq hn1 hΔ
  have hab : πT a * πT (t - a) = p := by
    have h := congrArg πT hαq
    simp only [map_add, map_sub, map_mul, map_natCast, map_zero, Algebra.algebraMap_self, AlgHom.commutes] at h
    rw [map_sub]
    linear_combination -h
  simp only [map_sub, map_mul, map_add, map_pow, AlgHom.commutes, map_natCast, Nat.cast_one, Nat.cast_add, map_one] at hab ⊢
  linear_combination (2 * πT a) * hab

end S_IharaTower_RungAssembly_map_delta_of_sq_sub
end P2MW
export P2MW.S_IharaTower_RungAssembly_map_delta_of_sq_sub (solution)
