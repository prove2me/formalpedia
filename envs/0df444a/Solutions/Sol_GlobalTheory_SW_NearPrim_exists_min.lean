-- Prove2me | solution 1 for GlobalTheory.SW.NearPrim.exists_min
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:28:28.404808+00:00
-- url     : https://prove2.me/submissions/1ce4d896-61e8-4944-b2d4-62cade099cbe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsBoundedMultipleNearInteger
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsNearlyPrimitive

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.NearPrim
namespace GlobalTheory.SW.NearPrim
theorem _root_.solution {E : Type} [Field E] [NumberField E] (S : Set E) (d : ℤ) (hd : d ≠ 0)
    (hS : ∀ x ∈ S, IsIntegral ℤ ((d : E) * x)) (h1 : (1 : E) ∈ S) :
    ∃ α ∈ S, ‖canonicalEmbedding E α‖ ≤ 1 ∧
      ∀ x ∈ S, ‖canonicalEmbedding E α‖ ≤ ‖canonicalEmbedding E x‖ := by
  have hfin : {x ∈ S | ‖canonicalEmbedding E x‖ ≤ 1}.Finite := by
    refine Set.Finite.of_finite_image (f := fun x => (d : E) * x)
      ((Embeddings.finite_of_norm_le E ℂ |(d : ℝ)|).subset ?_) ?_
    · rintro _ ⟨x, ⟨hx, hx1⟩, rfl⟩
      refine ⟨hS x hx, fun φ => ?_⟩
      have := (canonicalEmbedding.norm_le_iff x 1).1 hx1 φ
      rw [map_mul, norm_mul, map_intCast, Complex.norm_intCast]
      exact mul_le_of_le_one_right (abs_nonneg _) this
    · intro x _ y _ h
      exact mul_left_cancel₀ (Int.cast_ne_zero.2 hd) h
  have hone : ‖canonicalEmbedding E 1‖ ≤ 1 := (canonicalEmbedding.norm_le_iff 1 1).2 (by simp)
  obtain ⟨α, hα, hmin⟩ := Set.exists_min_image _ (fun x => ‖canonicalEmbedding E x‖) hfin
    ⟨1, h1, hone⟩
  refine ⟨α, hα.1, hα.2, fun x hx => ?_⟩
  by_cases h : ‖canonicalEmbedding E x‖ ≤ 1
  · exact hmin x ⟨hx, h⟩
  · exact hα.2.trans (not_le.1 h).le
end GlobalTheory.SW.NearPrim
