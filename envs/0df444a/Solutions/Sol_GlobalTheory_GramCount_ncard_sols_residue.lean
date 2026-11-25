-- Prove2me | solution 1 for GlobalTheory.GramCount.ncard_sols_residue
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:02:51.845246+00:00
-- url     : https://prove2.me/submissions/211ccab9-8542-4196-a2dc-2ffddd90b8ae

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PrimOfIsUnitDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardPrimitiveTupleExtensionsLeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NcardPrimitiveTuplesWithGramMatrixResidueRing
import Theorems.Thm_GlobalTheory_GramCount_eta_le
import Theorems.Thm_GlobalTheory_GramCount_ncard_sols_eta

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
variable {B : Type} [CommRing B]
namespace GlobalTheory.GramCount
theorem _root_.solution : ∀ {B : Type} [CommRing B] [Fintype B] (c : B →+* B), (∀ u, c (c u) = u) → ∀ (ω : B), IsUnit (ω - c ω) → (∀ t, c t = t → t ≠ 0 → IsUnit t) → ∀ (q : ℕ), 2 ≤ q → Fintype.card B = q ^ 2 → ∀ (m n : ℕ), 2 * m + 3 ≤ n → ∀ (G : Matrix (Fin m) (Fin m) B), (∀ a b, c (G b a) = G a b) → (q : ℝ) ^ (2 * n * m - m ^ 2) ≤ 2 * (Set.ncard (sols c n G) : ℝ) ∧ (Set.ncard (sols c n G) : ℝ) ≤ 2 * (q : ℝ) ^ (2 * n * m - m ^ 2) := by
  intro B _ _ c hc ω hω hf q hq hB m n hn G hG
  obtain ⟨h1, h2⟩ := ncard_sols_eta c hc ω hω hf q hq hB n m hn G hG
  have hη := eta_le hn
  have hQ : (0 : ℝ) ≤ (q : ℝ) ^ (2 * n * m - m ^ 2) := by positivity
  have := mul_le_mul_of_nonneg_right hη hQ
  constructor <;> nlinarith
end GlobalTheory.GramCount
