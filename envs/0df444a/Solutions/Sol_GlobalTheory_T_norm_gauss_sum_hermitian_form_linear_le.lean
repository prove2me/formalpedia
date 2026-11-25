-- Prove2me | solution 1 for GlobalTheory.T.norm_gauss_sum_hermitian_form_linear_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:02:21.361933+00:00
-- url     : https://prove2.me/submissions/e44ae174-b47c-45dc-88d5-4522d3e14a10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormGaussSumHermitianFormLinearLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PrimOfIsUnitDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormGaussSumHermitianFormLinearLeStatement
import Theorems.Thm_GlobalTheory_GramCount_norm_gauss_sum_ip_le


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
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {B : Type} [CommRing B] [Fintype B] (c : B →+* B), (∀ u, c (c u) = u) → ∀ (q : ℕ), 2 ≤ q → Fintype.card B = q ^ 2 → ∀ (χ : AddChar B ℂ), χ.IsPrimitive → (∀ u, χ (c u) = χ u) → ∀ (n : ℕ) (a : B), IsUnit (a + c a) → ∀ (v : Fin n → B), ‖∑ y : Fin n → B, χ (a * ip c y y + ip c y v)‖ ≤ (q : ℝ) ^ n := by
  first | exact @GlobalTheory.GramCount.norm_gauss_sum_ip_le | exact GlobalTheory.GramCount.norm_gauss_sum_ip_le | (intros; apply GlobalTheory.GramCount.norm_gauss_sum_ip_le <;> assumption)
end _root_.GlobalTheory.T
