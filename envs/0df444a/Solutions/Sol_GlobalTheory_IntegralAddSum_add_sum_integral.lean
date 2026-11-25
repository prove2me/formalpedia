-- Prove2me | solution 1 for GlobalTheory.IntegralAddSum.add_sum_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:53:51.960373+00:00
-- url     : https://prove2.me/submissions/95a8e70f-e731-472d-a4e9-0d000c234f7c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AddSumIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IntegralAddSum
namespace GlobalTheory.IntegralAddSum
theorem _root_.solution {A C K B : Type} [CommRing A] [CommRing C] [CommRing K] [CommRing B]
    (φ : A →+* K) (gc : C →+* B) (gk : K →+* B) {x y : B}
    (hx : ∃ (n : ℕ) (c : Fin n → C) (b : Fin n → K),
      (∀ m : Fin n, RingHom.IsIntegralElem φ (b m)) ∧ x = ∑ m : Fin n, gc (c m) * gk (b m))
    (hy : ∃ (n : ℕ) (c : Fin n → C) (b : Fin n → K),
      (∀ m : Fin n, RingHom.IsIntegralElem φ (b m)) ∧ y = ∑ m : Fin n, gc (c m) * gk (b m)) :
    ∃ (n : ℕ) (c : Fin n → C) (b : Fin n → K),
      (∀ m : Fin n, RingHom.IsIntegralElem φ (b m)) ∧ x + y = ∑ m : Fin n, gc (c m) * gk (b m) := by
  obtain ⟨n, c, b, hb, rfl⟩ := hx
  obtain ⟨n', c', b', hb', rfl⟩ := hy
  refine ⟨n + n', Fin.append c c', Fin.append b b', ?_, ?_⟩
  · intro m
    refine Fin.addCases (fun i => ?_) (fun i => ?_) m
    · rw [Fin.append_left]; exact hb i
    · rw [Fin.append_right]; exact hb' i
  · rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
end GlobalTheory.IntegralAddSum
