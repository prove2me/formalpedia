-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.KerPoint.inner_map_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:48:34.484807+00:00
-- url     : https://prove2.me/submissions/9389d781-3cd3-408a-8c58-bd84b6bfc7ca

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_ThetaCellCovers_VecClose
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_EqZeroOfLeSmall

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory PositivityTheory.Rg.BcB.E1
open scoped ENNReal Pointwise
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.KerPoint
namespace GlobalTheory.CompanionTheory.KerPoint
theorem _root_.solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (U : H →L[ℂ] H)
    (a b k₁ k₂ : H) (δ : ℝ) (ha : ‖a - k₁‖ ≤ δ) (hb : ‖b - k₂‖ ≤ δ) :
    ‖inner ℂ a (U b) - inner ℂ k₁ (U k₂)‖ ≤ ‖U‖ * δ * (‖k₂‖ + δ) + ‖k₁‖ * ‖U‖ * δ := by
  have e : inner ℂ a (U b) - inner ℂ k₁ (U k₂) = inner ℂ (a - k₁) (U b) + inner ℂ k₁ (U (b - k₂)) := by
    simp only [inner_sub_left, inner_sub_right, map_sub]
    ring
  have hbn : ‖b‖ ≤ ‖k₂‖ + δ := by
    have := norm_add_le (b - k₂) k₂
    rw [sub_add_cancel] at this
    linarith
  have hU : 0 ≤ ‖U‖ := norm_nonneg _
  have t1 : ‖(inner ℂ (a - k₁) (U b) : ℂ)‖ ≤ ‖U‖ * δ * (‖k₂‖ + δ) := by
    calc ‖(inner ℂ (a - k₁) (U b) : ℂ)‖ ≤ ‖a - k₁‖ * ‖U b‖ := norm_inner_le_norm _ _
      _ ≤ δ * (‖U‖ * (‖k₂‖ + δ)) := by
          have h2 : ‖U b‖ ≤ ‖U‖ * (‖k₂‖ + δ) :=
            (U.le_opNorm b).trans (mul_le_mul_of_nonneg_left hbn hU)
          exact mul_le_mul ha h2 (norm_nonneg _) ((norm_nonneg _).trans ha)
      _ = ‖U‖ * δ * (‖k₂‖ + δ) := by ring
  have t2 : ‖(inner ℂ k₁ (U (b - k₂)) : ℂ)‖ ≤ ‖k₁‖ * ‖U‖ * δ := by
    calc ‖(inner ℂ k₁ (U (b - k₂)) : ℂ)‖ ≤ ‖k₁‖ * ‖U (b - k₂)‖ := norm_inner_le_norm _ _
      _ ≤ ‖k₁‖ * (‖U‖ * δ) := by
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          exact (U.le_opNorm _).trans (mul_le_mul_of_nonneg_left hb hU)
      _ = ‖k₁‖ * ‖U‖ * δ := by ring
  rw [e]
  exact (norm_add_le _ _).trans (add_le_add t1 t2)
end GlobalTheory.CompanionTheory.KerPoint
