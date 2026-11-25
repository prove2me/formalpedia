-- Prove2me | solution 1 for GlobalTheory.SplitFinitePart.eq_comp_section
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:17:46.663198+00:00
-- url     : https://prove2.me/submissions/a128ea3d-ad3e-480f-8617-6f17b5045713

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsSectionOfIsIntegralHom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.SplitFinitePart
namespace GlobalTheory.SplitFinitePart
theorem _root_.solution {A B k : Type} [CommRing A] [CommRing B] [Algebra A B] [Field k] (β : B →+* k)
    (σ : B →ₐ[A] A) (y : Sp k) (h : spMap β y ∈ Set.range (spMap σ.toRingHom)) :
    β = (β.comp (algebraMap A B)).comp σ.toRingHom := by
  obtain ⟨Q, hQ⟩ := h
  ext b
  have h1 : b - algebraMap A B (σ b) ∈ (spMap σ.toRingHom Q).asIdeal := by
    change σ (b - algebraMap A B (σ b)) ∈ Q.asIdeal
    simp
  rw [hQ] at h1
  have h2 : β (b - algebraMap A B (σ b)) ∈ y.asIdeal := h1
  rw [(Ideal.eq_bot_of_prime y.asIdeal (h := y.isPrime)), Ideal.mem_bot, map_sub, sub_eq_zero] at h2
  exact h2
end GlobalTheory.SplitFinitePart
