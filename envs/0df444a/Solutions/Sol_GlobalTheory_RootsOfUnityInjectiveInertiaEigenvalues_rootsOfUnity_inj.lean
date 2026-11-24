-- Prove2me | solution 1 for GlobalTheory.RootsOfUnityInjectiveInertiaEigenvalues.rootsOfUnity_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:07:10.199796+00:00
-- url     : https://prove2.me/submissions/f76952a9-2a5d-48a8-856d-5eac4b86fb98

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RootsOfUnityInj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.RootsOfUnityInjectiveInertiaEigenvalues
namespace GlobalTheory.RootsOfUnityInjectiveInertiaEigenvalues
theorem _root_.solution {O k : Type} [CommRing O] [IsDomain O] [Field k] (f : O →+* k) {M : ℕ}
    (hM : (M : k) ≠ 0) {x y : O} (hx : x ^ M = 1) (hy : y ^ M = 1) (hf : f x = f y) : x = y := by
  have key : ∀ z : O, z ^ M = 1 → f z = 1 → z = 1 := by
    intro z hz hfz
    have h := geom_sum_mul z M
    rw [hz, sub_self] at h
    rcases mul_eq_zero.mp h with h1 | h1
    · exfalso
      apply hM
      have h2 := congrArg f h1
      simpa [map_sum, map_pow, hfz] using h2
    · exact sub_eq_zero.mp h1
  have hM0 : M ≠ 0 := by
    rintro rfl
    simp at hM
  have hsub : M - 1 + 1 = M := Nat.sub_add_cancel (Nat.pos_of_ne_zero hM0)
  have hyM : y ^ (M - 1) * y = 1 := by rw [← pow_succ, hsub, hy]
  have hz : (x * y ^ (M - 1)) ^ M = 1 := by
    rw [mul_pow, hx, ← pow_mul, mul_comm (M - 1) M, pow_mul, hy, one_pow, one_mul]
  have hfz : f (x * y ^ (M - 1)) = 1 := by
    rw [map_mul, map_pow, hf, ← pow_succ', hsub, ← map_pow, hy, map_one]
  have h1 := key _ hz hfz
  calc x = x * (y ^ (M - 1) * y) := by rw [hyM, mul_one]
    _ = (x * y ^ (M - 1)) * y := by ring
    _ = y := by rw [h1, one_mul]
end GlobalTheory.RootsOfUnityInjectiveInertiaEigenvalues
