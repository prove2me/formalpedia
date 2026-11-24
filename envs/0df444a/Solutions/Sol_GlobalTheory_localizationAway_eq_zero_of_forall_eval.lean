-- Prove2me | solution 1 for GlobalTheory.localizationAway_eq_zero_of_forall_eval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:19:01.528216+00:00
-- url     : https://prove2.me/submissions/2178b2b4-7a11-4baf-8bc0-f258aadb2c2a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsAlgHomLocalizationAwayOfRationalPoints

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Polynomial
namespace GlobalTheory
theorem _root_.solution {k : Type} [Field k] [Infinite k]
    (D : Polynomial k) (hD : D ≠ 0) (b : Localization.Away D)
    (h : ∀ t, D.eval t ≠ 0 → ∀ e : Localization.Away D →+* k,
      (∀ q, e (algebraMap (Polynomial k) _ q) = q.eval t) → e b = 0) : b = 0 := by
  obtain ⟨n, q, hq⟩ := IsLocalization.Away.surj D b
  have hq0 : q * D = 0 := by
    apply Polynomial.funext
    intro t
    rw [Polynomial.eval_mul, Polynomial.eval_zero]
    by_cases ht : D.eval t = 0
    · rw [ht, mul_zero]
    · have hu : IsUnit (Polynomial.evalRingHom t D) := isUnit_iff_ne_zero.mpr ht
      have he : ∀ q, (IsLocalization.Away.lift (S := Localization.Away D) D hu)
          (algebraMap (Polynomial k) _ q) = q.eval t := fun q =>
        IsLocalization.Away.lift_eq D hu q
      have h0 := h t ht _ he
      have h1 := congrArg (IsLocalization.Away.lift (S := Localization.Away D) D hu) hq
      rw [map_mul, h0, zero_mul, he] at h1
      rw [← h1, zero_mul]
  have hq1 : q = 0 := (mul_eq_zero.mp hq0).resolve_right hD
  rw [hq1, map_zero] at hq
  exact ((IsLocalization.Away.algebraMap_isUnit D).pow n).mul_left_eq_zero.mp hq
end GlobalTheory
