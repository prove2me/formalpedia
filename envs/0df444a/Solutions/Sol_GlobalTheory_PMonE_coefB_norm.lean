-- Prove2me | solution 1 for GlobalTheory.PMonE.coefB_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:17:26.293132+00:00
-- url     : https://prove2.me/submissions/9fee9e6a-d79a-4146-b3f6-3dfc2074a1a1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RowTEqRowS
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsWindowRadii
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdditiveSystemGeneralLemmaAllOrdersStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FrobeniusWindowSeriesTermNormLeRowBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormFrobeniusWindowSeriesTermMonoStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WindowSummedRowPowEqAdditiveSystemPowerSumStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormalizedRowCoefficientMatricesDetNormStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormalOfInvMulStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardWindowZerosEqIntegralAdditiveSystemStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardWindowZerosInnerEqShiftedOuterStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FrobeniusPolydiscWindowsSurjectiveBoundsZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PMonE
open Finset Matrix
namespace GlobalTheory.PMonE
theorem _root_.solution {F : Type} [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p] {h : ℕ}
    (ϖ : F) (lam π : Fin h → F) (L U : ℕ)
    (hb : ∀ (r j : Fin h) (n : ℤ), ‖term p ϖ lam π r j n‖ ≤ ‖lam r * π r ^ p ^ (r : ℕ)‖ ∧
      (0 < n → ‖term p ϖ lam π r j n‖ < ‖lam r * π r ^ p ^ (r : ℕ)‖)) :
    (∀ m r j, ‖coefB p ϖ lam π L U m r j‖ ≤ 1) ∧ (∀ m, L < m → ∀ r j, ‖coefB p ϖ lam π L U m r j‖ < 1) := by
  have key : ∀ m r j, ‖coefB p ϖ lam π L U m r j‖ ≤ 1 ∧ (L < m → ‖coefB p ϖ lam π L U m r j‖ < 1) := by
    intro m r j
    simp only [coefB, Matrix.of_apply]
    split_ifs with hm
    · rw [norm_pow, norm_div]
      obtain ⟨h1, h2⟩ := hb r j ((m : ℤ) - L)
      have hpos : p ^ (h - (r : ℕ)) ≠ 0 := pow_ne_zero _ (Fact.out : p.Prime).ne_zero
      rcases eq_or_lt_of_le (norm_nonneg (lam r * π r ^ p ^ (r : ℕ))) with hc | hc
      · rw [← hc, div_zero, zero_pow hpos]
        exact ⟨zero_le_one, fun _ => zero_lt_one⟩
      · refine ⟨pow_le_one₀ (div_nonneg (norm_nonneg _) hc.le) ((div_le_one hc).2 h1), fun hLm => ?_⟩
        exact pow_lt_one₀ (div_nonneg (norm_nonneg _) hc.le) ((div_lt_one hc).2 (h2 (by omega))) hpos
    · simp
  exact ⟨fun m r j => (key m r j).1, fun m hm r j => (key m r j).2 hm⟩
end GlobalTheory.PMonE
