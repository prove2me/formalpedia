-- Prove2me | solution 1 for GlobalTheory.highest_weight_antitone
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:39:13.691644+00:00
-- url     : https://prove2.me/submissions/3b4b0984-e71d-4e40-bf1c-1d2382eab620

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_Sl2NonnegWeightOfHighestWeightVector
import Theorems.Thm_GlobalTheory_sl2_nonneg_weight_of_highest_weight_vector

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {m : ℕ} (e : Fin m → Fin m → Module.End K V)
    (he : ∀ i j k l, e i j * e k l - e k l * e i j = (if j = k then e i l else 0) - (if l = i then e k j else 0))
    (W : Submodule K V) [FiniteDimensional K W] (hW : ∀ i j, ∀ w ∈ W, e i j w ∈ W)
    (v : V) (hvW : v ∈ W) (hv0 : v ≠ 0) (κ : Fin m → ℤ) (hv : ∀ i j, i < j → e i j v = 0) (hκ : ∀ i, e i i v = (κ i : K) • v) : Antitone κ := by
  intro a b hab
  rcases hab.lt_or_eq with h | h
  · have hne : a ≠ b := h.ne
    have hEF : e a b * e b a - e b a * e a b = e a a - e b b := by
      simpa only [↓reduceIte] using he a b b a
    have hHF : (e a a - e b b) * e b a - e b a * (e a a - e b b) = -(e b a + e b a) := by
      have h1 := he a a b a
      have h2 := he b b b a
      simp only [if_neg hne, ↓reduceIte, zero_sub, sub_zero] at h1 h2
      calc (e a a - e b b) * e b a - e b a * (e a a - e b b)
          = (e a a * e b a - e b a * e a a) - (e b b * e b a - e b a * e b b) := by
            rw [sub_mul, mul_sub]
            abel
        _ = -(e b a + e b a) := by
            rw [h1, h2]
            abel
    have hHv : (e a a - e b b) v = (((κ a - κ b : ℤ)) : K) • v := by
      rw [LinearMap.sub_apply, hκ, hκ]
      push_cast
      rw [sub_smul]
    have h0 := sl2_nonneg_weight_of_highest_weight_vector (e a b) (e b a) (e a a - e b b) hEF hHF W
      (hW b a) v hvW hv0 (κ a - κ b) (hv a b h) hHv
    linarith
  · subst h
    exact le_rfl
end GlobalTheory
