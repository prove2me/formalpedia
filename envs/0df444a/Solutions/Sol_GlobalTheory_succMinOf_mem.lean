-- Prove2me | solution 1 for GlobalTheory.succMinOf_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:48:51.896388+00:00
-- url     : https://prove2.me/submissions/fe77d96c-fc18-4f99-9910-22c9d096d2a5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsLinearIndependentNormLeSuccMin
import Theorems.Thm_GlobalTheory_mem_succMinRadii_of_lt

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
open scoped Pointwise
open GlobalTheory
variable (K : Type*) [DivisionRing K] {V : Type*} [AddCommGroup V] [Module K V]
variable {K}
variable {N N' : V → ℝ} {S S' : Set V} {i j : ℕ} {r : ℝ}
namespace GlobalTheory
theorem _root_.solution (hfin : ∀ R, {x | x ∈ S ∧ N x ≤ R}.Finite)
    (hi : (i : Cardinal) ≤ Module.rank K (span K S)) :
    succMinOf K N S i ∈ succMinRadii K N S i := by
  set s := succMinOf K N S i with hs
  have hA : ({x | x ∈ S ∧ N x ≤ s + 1} ∩ {x | s < N x}).Finite := (hfin _).inter_of_left _
  obtain ⟨r, hsr, hr1, hr⟩ : ∃ r, s < r ∧ r ≤ s + 1 ∧
      ∀ x ∈ ({x | x ∈ S ∧ N x ≤ s + 1} ∩ {x | s < N x}), r < N x := by
    rcases ({x | x ∈ S ∧ N x ≤ s + 1} ∩ {x | s < N x}).eq_empty_or_nonempty with h | h
    · exact ⟨s + 1, by linarith, le_rfl, by simp [h]⟩
    · obtain ⟨x, hx, hmin⟩ := Set.exists_min_image _ N hA h
      have h1 : s < N x := hx.2
      have h2 : N x ≤ s + 1 := hx.1.2
      exact ⟨(s + N x) / 2, by linarith, by linarith, fun y hy => by linarith [hmin y hy]⟩
  obtain ⟨-, v, hv, hS⟩ := mem_succMinRadii_iff.1 (mem_succMinRadii_of_lt hi hsr)
  refine mem_succMinRadii_iff.2 ⟨succMinOf_nonneg, v, hv, fun k => ⟨(hS k).1, ?_⟩⟩
  by_contra hlt
  exact absurd (hr (v k) ⟨⟨(hS k).1, (hS k).2.trans hr1⟩, not_le.1 hlt⟩) (not_lt.2 (hS k).2)
end GlobalTheory
