-- Prove2me | solution 1 for GlobalTheory.InjectiveAlgebraMapTorsionFree.algebraMap_injective_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:47:55.594657+00:00
-- url     : https://prove2.me/submissions/bd649616-fdf8-4a8c-9d51-f3f529e74f3b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsInjectiveNormLeOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.InjectiveAlgebraMapTorsionFree
variable (p : ℕ) [Fact (Nat.Prime p)]
namespace GlobalTheory.InjectiveAlgebraMapTorsionFree
theorem _root_.solution (D : Type) [CommRing D] [IsDomain D] [Algebra ℤ_[p] D]
    (hp : (p : D) ≠ 0) : Function.Injective (algebraMap ℤ_[p] D) := by
  by_contra hinj
  have hker : RingHom.ker (algebraMap ℤ_[p] D) ≠ ⊥ := fun h =>
    hinj ((RingHom.injective_iff_ker_eq_bot _).mpr h)
  obtain ⟨n, hn⟩ := PadicInt.ideal_eq_span_pow_p hker
  have hmem : (p : ℤ_[p]) ^ n ∈ RingHom.ker (algebraMap ℤ_[p] D) := by
    rw [hn]
    exact Ideal.mem_span_singleton_self _
  rw [RingHom.mem_ker, map_pow, map_natCast] at hmem
  exact hp (pow_eq_zero_iff'.mp hmem).1
end GlobalTheory.InjectiveAlgebraMapTorsionFree
