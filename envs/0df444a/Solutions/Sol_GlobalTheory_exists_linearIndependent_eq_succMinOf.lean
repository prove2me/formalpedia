-- Prove2me | solution 1 for GlobalTheory.exists_linearIndependent_eq_succMinOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:55:12.016458+00:00
-- url     : https://prove2.me/submissions/b0826d92-fdf6-48ab-9913-b46ebfc625ef

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsLinearIndependentNormLeSuccMin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsLinearIndependentSqrtEqSuccMinQuad
import Theorems.Thm_GlobalTheory_mem_span_of_lt_succMinOf
import Theorems.Thm_GlobalTheory_succMinOf_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module Submodule
open GlobalTheory
variable {K : Type*} [DivisionRing K] {V : Type*} [AddCommGroup V] [Module K V]
  {N : V → ℝ} {S : Set V} {n : ℕ}
namespace GlobalTheory
theorem _root_.solution (hfin : ∀ R, {x | x ∈ S ∧ N x ≤ R}.Finite)
    (hN : ∀ x ∈ S, 0 ≤ N x) (hn : (n : Cardinal) ≤ Module.rank K (span K S)) :
    ∃ v : Fin n → V, LinearIndependent K v ∧ (∀ j, v j ∈ S) ∧
      ∀ j : Fin n, N (v j) = succMinOf K N S (j + 1) := by
  induction n with
  | zero => exact ⟨Fin.elim0, linearIndependent_empty_type, fun j => j.elim0, fun j => j.elim0⟩
  | succ m ih =>
    obtain ⟨v, hv, hS, hvN⟩ := ih ((Nat.cast_le.2 (Nat.le_succ m)).trans hn)
    obtain ⟨-, w, hw, hwS⟩ := mem_succMinRadii_iff.1 (succMinOf_mem hfin hn)
    obtain ⟨k, hk⟩ : ∃ k, w k ∉ span K (Set.range v) := by
      by_contra! h
      have h1 : span K (Set.range w) ≤ span K (Set.range v) :=
        span_le.2 (Set.range_subset_iff.2 h)
      have : Module.Finite K (span K (Set.range v)) :=
        Module.Finite.span_of_finite K (Set.finite_range v)
      have h2 := Submodule.finrank_mono h1
      rw [finrank_span_eq_card hw, finrank_span_eq_card hv] at h2
      simp at h2
    have hk' : N (w k) = succMinOf K N S (m + 1) := by
      refine le_antisymm (hwS k).2 (not_lt.1 fun h => hk ?_)
      exact span_mono (Set.image_subset_range _ _)
        (mem_span_of_lt_succMinOf hv hS (fun j => (hvN j).le) le_rfl (hwS k).1
          (hN _ (hwS k).1) h)
    refine ⟨Fin.snoc v (w k), linearIndependent_finSnoc.2 ⟨hv, hk⟩, fun j => ?_, fun j => ?_⟩
    · refine Fin.lastCases ?_ (fun j => ?_) j
      · simpa using (hwS k).1
      · simpa using hS j
    · refine Fin.lastCases ?_ (fun j => ?_) j
      · simpa using hk'
      · simpa using hvN j
end GlobalTheory
