-- Prove2me | solution 1 for GlobalTheory.finite_and_ncard_setOf_norm_le_of_rank
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:48:55.212593+00:00
-- url     : https://prove2.me/submissions/4f61e889-4910-4bae-bc3e-13d57e97cfbf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FiniteAndNcardSetOfSubmoduleLeRelIndexEqLe
import Theorems.Thm_GlobalTheory_card_le_of_family_separated
import Theorems.Thm_GlobalTheory_finite_and_ncard_le_of_forall_finset
import Theorems.Thm_GlobalTheory_exists_zsmul_mem_span_of_linearIndependent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open GlobalTheory
open MeasureTheory Metric
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
namespace GlobalTheory
theorem _root_.solution (L : Submodule ℤ E) [Module.Finite ℤ L] {n : ℕ}
    (hn : finrank ℤ L = n) {v : Fin n → L} (hv : LinearIndependent ℤ v) {d R : ℝ} (hd : 0 < d)
    (hR : 0 ≤ R) (hL : ∀ x ∈ L, x ≠ 0 → d ≤ ‖x‖) :
    {x : L | ‖(x : E)‖ ≤ R}.Finite ∧
      (({x : L | ‖(x : E)‖ ≤ R}.ncard : ℕ) : ℝ) ≤ (1 + 2 * R / d) ^ n := by
  let W : Submodule ℝ E := Submodule.span ℝ (Set.range fun i => (v i : E))
  haveI : FiniteDimensional ℝ W := FiniteDimensional.span_of_finite ℝ (Set.finite_range _)
  have hW : finrank ℝ W ≤ n := by
    exact (finrank_range_le_card (R := ℝ) (fun i => (v i : E))).trans (Fintype.card_fin n).le
  have hmem : ∀ x : L, (x : E) ∈ W := by
    intro x
    obtain ⟨k, hk, hx⟩ := exists_zsmul_mem_span_of_linearIndependent hn hv x
    have h1 : Submodule.span ℤ (Set.range v) ≤ (W.restrictScalars ℤ).comap L.subtype := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact Submodule.subset_span ⟨i, rfl⟩
    have h2 : (k : ℝ) • (x : E) ∈ W := by
      rw [Int.cast_smul_eq_zsmul]
      exact h1 hx
    exact (W.smul_mem_iff (by exact_mod_cast hk)).1 h2
  refine finite_and_ncard_le_of_forall_finset _ _ fun s hs => ?_
  refine (card_le_of_family_separated s (fun x : L => (⟨x, hmem x⟩ : W)) hd hR
    (fun i hi => hs hi) (fun i _ j _ hij => ?_)).trans ?_
  · exact hL _ (L.sub_mem i.2 j.2) (sub_ne_zero.2 fun h => hij (Subtype.ext h))
  · exact pow_le_pow_right₀ (le_add_of_nonneg_right (by positivity)) hW
end GlobalTheory
