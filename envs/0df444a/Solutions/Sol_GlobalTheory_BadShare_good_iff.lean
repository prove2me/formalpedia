-- Prove2me | solution 1 for GlobalTheory.BadShare.good_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:07:42.802013+00:00
-- url     : https://prove2.me/submissions/a64f8921-d5bf-4922-a427-753732cb8ee4

import Mathlib
import Definitions.Def_Formalism_CyclotomicNorms_StatementT
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Theorems.Thm_GlobalTheory_BadShare_mem_sqSet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial Classical
open GlobalTheory GlobalTheory.BadShare
variable (g : ℕ) [Fact g.Prime]
variable {g}
open Polynomial Classical
variable (g : ℕ) [Fact g.Prime]
variable {g}
namespace GlobalTheory.BadShare
namespace _root_.GlobalTheory.BadShare
theorem _root_.solution {ι : Type} {m N : ℕ} {ch : ι → Fin m → (ZMod g)ˣ} {F : ι → (ZMod g)[X]} :
    _root_.GlobalTheory.BadShare.Good g N ch F ↔ (∀ v, F v ∈ _root_.GlobalTheory.BadShare.sqSet g N) ∧
      (∀ v, _root_.GlobalTheory.BadShare.RootsApart g N (F v)) ∧
      (∀ v j, _root_.GlobalTheory.BadShare.RootsAvoid g (ch v j) (F v) ∧ _root_.GlobalTheory.BadShare.RootsAvoid g (ch v j)⁻¹ (F v)) ∧
      (¬ ∃ a : ℕ, 1 ≤ a ∧ 2 * a ≤ N ∧ ∀ v, _root_.GlobalTheory.BadShare.HasDiv g a (F v)) ∧
      ∃ v, _root_.GlobalTheory.BadShare.HasPrimeFactor g N (F v) := by
  unfold _root_.GlobalTheory.BadShare.Good
  constructor
  · rintro ⟨⟨h1, h2, h3, h4, h5, h6⟩, ⟨-, -, -, h4', -, -⟩⟩
    refine ⟨fun v => _root_.GlobalTheory.BadShare.mem_sqSet.2 ⟨(h1 v).1, (h1 v).2.1, h2 v, (h1 v).2.2⟩,
      fun v l hl hB x hx y hy hxy => h3 l hl hB v x hx y hy hxy,
      fun v j => ⟨fun l hl hlg x hx => h4 l hl hlg v j x hx, fun l hl hlg x hx => h4' l hl hlg v j x hx⟩, ?_, ?_⟩
    · rintro ⟨a, ha1, ha2, hall⟩
      obtain ⟨v, hv⟩ := h5 a ha1 ha2
      exact hv (hall v)
    · obtain ⟨v, q, hq⟩ := h6
      exact ⟨v, q, hq⟩
  · rintro ⟨h1, h2, h3, h4, v, hv⟩
    have hA : ∀ w, (F w).Monic ∧ (F w).natDegree = N ∧ (F w).coeff 0 ≠ 0 := fun w =>
      ⟨(_root_.GlobalTheory.BadShare.mem_sqSet.1 (h1 w)).1, (_root_.GlobalTheory.BadShare.mem_sqSet.1 (h1 w)).2.1,
        (_root_.GlobalTheory.BadShare.mem_sqSet.1 (h1 w)).2.2.2⟩
    have hS : ∀ w, Squarefree (F w) := fun w => (_root_.GlobalTheory.BadShare.mem_sqSet.1 (h1 w)).2.2.1
    have hD : ∀ a : ℕ, 1 ≤ a → 2 * a ≤ N → ∃ w, ¬∃ q : (ZMod g)[X], q ∣ F w ∧ q.natDegree = a := by
      intro a ha1 ha2
      by_contra hc
      push_neg at hc
      exact h4 ⟨a, ha1, ha2, hc⟩
    exact ⟨⟨hA, hS, fun l hl hB w => h2 w l hl hB, fun l hl hlg w j => (h3 w j).1 l hl hlg, hD, v, hv⟩,
      ⟨hA, hS, fun l hl hB w => h2 w l hl hB, fun l hl hlg w j => (h3 w j).2 l hl hlg, hD, v, hv⟩⟩
end _root_.GlobalTheory.BadShare
end GlobalTheory.BadShare
