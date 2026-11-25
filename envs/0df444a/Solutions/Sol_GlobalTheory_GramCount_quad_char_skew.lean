-- Prove2me | solution 1 for GlobalTheory.GramCount.quad_char_skew
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:32:04.054825+00:00
-- url     : https://prove2.me/submissions/06f52b52-8be1-4fab-8ab5-6e503d87553b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PrimOfIsUnitDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormGaussSumHermitianFormLinearLeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardHermitianQuadricAffineSubspaceResidueRing
import Theorems.Thm_GlobalTheory_GramCount_exists_trace_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.GramCount
open scoped Classical
open GlobalTheory GlobalTheory.GramCount
variable {B : Type} [CommRing B] [Fintype B]
omit [Fintype B]
namespace GlobalTheory.GramCount
theorem _root_.solution (c : B →+* B) (hc : ∀ u, c (c u) = u) {ω : B} (hω : IsUnit (ω - c ω))
    (χ : AddChar B ℂ) (hχc : ∀ u, χ (c u) = χ u) {a w : B} (ha : c a = -a) (hw : c w = w) :
    χ (a * w) = 1 := by
  obtain ⟨θ, e, hθ, -, -⟩ := exists_trace_one c hc hω
  have h1 : a * w = θ * (a * w) + c (θ * (-(a * w))) := by
    simp only [map_mul, map_neg, ha, hw]
    linear_combination (-(a * w)) * hθ
  rw [h1, AddChar.map_add_eq_mul, hχc, ← AddChar.map_add_eq_mul]
  simp
end GlobalTheory.GramCount
