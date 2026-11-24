-- Prove2me | solution 1 for GlobalTheory.PowerBound.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:43:48.496979+00:00
-- url     : https://prove2.me/submissions/d89a2343-2264-4959-ac51-ba0b5d808703

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_Imports
import Theorems.Thm_GlobalTheory_PowerBound_pow_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.PowerBound
namespace GlobalTheory.PowerBound
theorem _root_.solution : ∀ {A : Type} [inst : CommRing A] (a d : A) (n : ℕ) {x : A},
    x ∈ (Ideal.span {a} ⊔ Ideal.span {d}) ^ (n + (1 : ℕ)) →
      ∃ (u : A), ∃ w ∈ (Ideal.span {a} ⊔ Ideal.span {d}) ^ n, x = a ^ (n + (1 : ℕ)) * u + d * w := by
  intro A _ a d n x hx
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 (pow_le a d n hx)
  obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton'.1 hy
  obtain ⟨w, hw, rfl⟩ := Ideal.mem_span_singleton_mul.1 hz
  exact ⟨u, w, hw, by ring⟩
end GlobalTheory.PowerBound
