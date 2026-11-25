-- Prove2me | solution 1 for GlobalTheory.CurveProductSmooth.JointlySmooth.translate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:50:40.730476+00:00
-- url     : https://prove2.me/submissions/c2cd9e3a-bfc1-4ef2-8bdb-f41397eab99b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocallyIntegrableRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SmoothAlongCurveProductsStable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ContDiff
open GlobalTheory
open GlobalTheory.CurveProductSmooth
variable {G : Type} [Group G] {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  (ρ : G →* (K →L[ℂ] K)) {P : Type} (A : Set P) (e : P → ℝ → G)
variable {ρ A e}
namespace GlobalTheory.CurveProductSmooth
namespace JointlySmooth
theorem _root_.solution {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {Φ : E → K}
    (h : JointlySmooth ρ A e Φ) (m : List (P × (E → ℝ)))
    (hm : ∀ a ∈ m, a.1 ∈ A ∧ ContDiff ℝ ∞ a.2) :
    JointlySmooth ρ A e fun t => ρ (m.map fun a => e a.1 (a.2 t)).prod (Φ t) := by
  intro F _ _ g hg l hl
  have h1 := h F g hg (l ++ m.map fun a => (a.1, a.2 ∘ g)) (by
    intro a ha
    rcases List.mem_append.1 ha with ha | ha
    · exact hl a ha
    · obtain ⟨b, hb, rfl⟩ := List.mem_map.1 ha
      exact ⟨(hm b hb).1, (hm b hb).2.comp hg⟩)
  simp only [List.map_append, List.prod_append, map_mul, List.map_map] at h1
  exact h1
end JointlySmooth
end GlobalTheory.CurveProductSmooth
