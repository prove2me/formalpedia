-- Prove2me | solution 1 for GlobalTheory.SaturatedNotDvd.exists_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:32:57.888721+00:00
-- url     : https://prove2.me/submissions/206e25f2-966e-4593-b1c3-ef3028b27f47

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsSaturated

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1
open GlobalTheory GlobalTheory.SaturatedNotDvd
namespace GlobalTheory.SaturatedNotDvd
theorem _root_.solution {A : Type u_1} [CommRing A] [IsNoetherianRing A] [IsLocalRing A] {x : A}
    (hx : ¬ IsUnit x) {K : Ideal A} (hK : K ≠ ⊥) (hs : ∀ u, x * u ∈ K → u ∈ K) :
    ∃ u ∈ K, ¬ x ∣ u := by
  by_contra hall
  push_neg at hall
  apply hK
  apply Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (Ideal.span {x}) K (IsNoetherian.noetherian K)
  · intro u hu
    obtain ⟨u', rfl⟩ := hall u hu
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self x) (hs u' hu)
  · rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    exact (Ideal.span_singleton_le_iff_mem _).2 ((IsLocalRing.mem_maximalIdeal x).2 hx)
end GlobalTheory.SaturatedNotDvd
