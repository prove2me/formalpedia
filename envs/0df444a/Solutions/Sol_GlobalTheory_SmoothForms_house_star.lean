-- Prove2me | solution 1 for GlobalTheory.SmoothForms.house_star
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:34:39.609858+00:00
-- url     : https://prove2.me/submissions/41112b6e-f8a8-480d-b68e-3a0128b3afe2

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ContDiff Topology
open NumberField Matrix
open GlobalTheory GlobalTheory.SmoothForms
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open scoped ContDiff Topology
open NumberField Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.SmoothForms
namespace _root_.GlobalTheory.SmoothForms
theorem _root_.solution (a : E) : house (star a) = house a := by
  have hs : star a = (NumberField.IsCMField.complexConj E) a := rfl
  have key : ∀ φ : E →+* ℂ, ‖canonicalEmbedding E (star a) φ‖ = ‖canonicalEmbedding E a φ‖ := by
    intro φ
    rw [canonicalEmbedding.apply_at, canonicalEmbedding.apply_at, hs,
      NumberField.IsCMField.complexEmbedding_complexConj, Complex.norm_conj]
  unfold house
  apply le_antisymm
  · exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun φ => (key φ).le.trans (norm_le_pi_norm _ φ)
  · exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun φ => (key φ).ge.trans (norm_le_pi_norm _ φ)
end _root_.GlobalTheory.SmoothForms
end GlobalTheory.SmoothForms
