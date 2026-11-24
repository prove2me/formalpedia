-- Prove2me | solution 1 for GlobalTheory.QNorm.IsQuad.exists_base_value
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:42:36.773802+00:00
-- url     : https://prove2.me/submissions/5ff5b669-70b8-41ff-9718-9ffb5b6e1e75

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_HeightOneSpectrumPlacesOverFiniteSet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ValuationUnramifiedOfUnit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
open GlobalTheory GlobalTheory.QNorm
namespace GlobalTheory.QNorm
namespace IsQuad
theorem _root_.solution {F E : Type} [Field F] [Field E] [Algebra F E] {δ : F} {θ : E}
    {σ : E ≃ₐ[F] E} (h : IsQuad δ θ σ) (w : Valuation E ℤᵐ⁰) (h2 : w 2 = 1)
    (hδ : w (algebraMap F E δ) = 1) (x : E) : ∃ u : F, w x = w (algebraMap F E u) := by
  obtain ⟨a, b, hx⟩ := h.span x
  have hθ : w θ = 1 := by
    rw [← h.sq, map_pow] at hδ
    exact (pow_eq_one_iff_of_nonneg zero_le two_ne_zero).1 hδ
  set y : E := algebraMap F E a - algebraMap F E b * θ with hy
  have ha : w (x + y) = w (algebraMap F E a) := by
    have : x + y = 2 * algebraMap F E a := by rw [hx, hy]; ring
    rw [this, map_mul, h2, one_mul]
  have hb : w (x - y) = w (algebraMap F E b) := by
    have : x - y = 2 * algebraMap F E b * θ := by rw [hx, hy]; ring
    rw [this, map_mul, map_mul, h2, hθ, one_mul, mul_one]
  have hn : x * y = algebraMap F E (a ^ 2 - δ * b ^ 2) := by
    rw [hx, hy, map_sub, map_mul, map_pow, map_pow, ← h.sq]; ring
  rcases lt_trichotomy (w x) (w y) with hlt | heq | hgt
  · have h1 : w y = w (algebraMap F E a) := by rw [← ha, w.map_add_eq_of_lt_right hlt]
    have hy0 : w y ≠ 0 := (lt_of_le_of_lt zero_le hlt).ne'
    refine ⟨(a ^ 2 - δ * b ^ 2) / a, ?_⟩
    rw [map_div₀, map_div₀, ← hn, ← h1, map_mul, mul_div_assoc, div_self hy0, mul_one]
  · have h1 : w (algebraMap F E a) ≤ w x := by
      rw [← ha]; exact (w.map_add x y).trans (max_le le_rfl heq.ge)
    have h3 : w (algebraMap F E b) ≤ w x := by
      rw [← hb]; exact (w.map_sub x y).trans (max_le le_rfl heq.ge)
    have h4 : w x ≤ max (w (algebraMap F E a)) (w (algebraMap F E b)) := by
      have := w.map_add (algebraMap F E a) (algebraMap F E b * θ)
      rwa [← hx, map_mul, hθ, mul_one] at this
    rcases le_max_iff.1 h4 with h5 | h5
    · exact ⟨a, le_antisymm h5 h1⟩
    · exact ⟨b, le_antisymm h5 h3⟩
  · exact ⟨a, by rw [← ha, w.map_add_eq_of_lt_left hgt]⟩
end IsQuad
end GlobalTheory.QNorm
