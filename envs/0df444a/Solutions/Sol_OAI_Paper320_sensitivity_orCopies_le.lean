-- Prove2me | solution 1 for OAI.Paper320.sensitivity_orCopies_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T02:54:41.383666+00:00
-- url     : https://prove2.me/submissions/69db968e-c262-4ab1-87a9-751a9010e4d2

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Sensitivity/Or.lean:L40-L71
-- (upload_full_project.md Phase 4): solution for node OAI.Paper320.sensitivity_orCopies_le. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_SensitivitySeparation
import Definitions.Def_OAI_Combinatorics_Sensitivity_HammingBase
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveProfiles
import Definitions.Def_OAI_Combinatorics_Sensitivity_Basic
import Definitions.Def_OAI_Combinatorics_Sensitivity_InitialPredicates
import Definitions.Def_OAI_Combinatorics_Sensitivity_Tournament
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveDefinitions
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveBlocks
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveSets
import Definitions.Def_OAI_Combinatorics_Sensitivity_TournamentCounts
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveFailures
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveCandidates
import Definitions.Def_OAI_Combinatorics_Sensitivity_Tower
import Definitions.Def_OAI_Combinatorics_Sensitivity_TowerProfiles
import Definitions.Def_OAI_Combinatorics_Sensitivity_ProfileArithmetic
import Definitions.Def_OAI_Combinatorics_Sensitivity_Composition
import Definitions.Def_OAI_Combinatorics_Sensitivity_Or

-- ---- from OAI.Combinatorics.Sensitivity.Basic ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-! Finite Boolean flips and the exact maximum/witness interfaces for sensitivity. -/

noncomputable section
open scoped Classical

namespace Paper320

variable {I J K : Type}

theorem flip_singleton_other (x : I → Bool) {i j : I} (h : j ≠ i) :
    flip x {i} j = x j := by
  simp [flip, h]

theorem flip_prod_same (x : J × I → Bool) (j : J) (i : I) :
    (fun a => flip x {(j, i)} (j, a)) = flip (fun a => x (j, a)) {i} := by
  funext a
  simp [flip]

theorem flip_prod_other (x : J × I → Bool) {j k : J} (i : I) (hk : k ≠ j) :
    (fun a => flip x {(j, i)} (k, a)) = fun a => x (k, a) := by
  funext a
  simp [flip, hk]

section Finite

variable [Fintype I]

theorem sensitivity_le (f : (I → Bool) → Bool) {n : ℕ}
    (h : ∀ x, sensitivityAt f x ≤ n) : sensitivity f ≤ n :=
  Finset.sup_le fun x _ => h x

end Finite
end Paper320

end

end OAI

-- ---- from OAI.Combinatorics.Sensitivity.Composition ----
namespace OAI

/-! Disjoint Boolean composition, with each child retaining its own raw coordinates. -/

noncomputable section
open scoped Classical BigOperators

namespace Paper320

variable {I J : Type}

theorem compose_flip_sensitive_iff (f : (I → Bool) → Bool) (g : (J → Bool) → Bool)
    (x : I × J → Bool) (i : I) (j : J) :
    compose f g (flip x {(i, j)}) ≠ compose f g x ↔
      g (flip (fun a => x (i, a)) {j}) ≠ g (fun a => x (i, a)) ∧
      f (flip (fun k => g (fun a => x (k, a))) {i}) ≠
        f (fun k => g (fun a => x (k, a))) := by
  by_cases hg : g (flip (fun a => x (i, a)) {j}) = g (fun a => x (i, a))
  · have he : (fun k => g (fun a => flip x {(i, j)} (k, a))) =
        fun k => g (fun a => x (k, a)) := by
      funext k
      by_cases hk : k = i
      · subst k
        rw [flip_prod_same, hg]
      · rw [flip_prod_other x j hk]
    simp only [compose, he, ne_eq, not_true_eq_false, hg, false_and]
  · have hn : g (flip (fun a => x (i, a)) {j}) = !(g (fun a => x (i, a))) := by
      cases h₁ : g (flip (fun a => x (i, a)) {j}) <;>
        cases h₂ : g (fun a => x (i, a)) <;> simp_all
    have he : (fun k => g (fun a => flip x {(i, j)} (k, a))) =
        flip (fun k => g (fun a => x (k, a))) {i} := by
      funext k
      by_cases hk : k = i
      · subst k
        rw [flip_prod_same, flip_singleton_self, hn]
      · rw [flip_prod_other x j hk, flip_singleton_other _ hk]
    simp only [compose, he, ne_eq, hg, not_false_eq_true, true_and]

section Finite
variable [Fintype I] [Fintype J]

theorem sensitivityAt_compose (f : (I → Bool) → Bool) (g : (J → Bool) → Bool)
    (x : I × J → Bool) :
    sensitivityAt (compose f g) x =
      ∑ i ∈ Finset.univ.filter (fun i =>
        f (flip (fun k => g (fun a => x (k, a))) {i}) ≠
          f (fun k => g (fun a => x (k, a)))),
        sensitivityAt g (fun a => x (i, a)) := by
  simp only [sensitivityAt, Finset.card_eq_sum_ones, Finset.sum_filter,
    compose_flip_sensitive_iff, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : f (flip (fun k => g (fun a => x (k, a))) {i}) ≠
      f (fun k => g (fun a => x (k, a)))
  · simp [hi]
  · simp [hi]

end Finite
end Paper320

end

end OAI

-- ---- from OAI.Combinatorics.Sensitivity.Or ----
namespace OAI

/-! Balancing the zero and one sensitivities by an OR of disjoint copies. -/

noncomputable section
open scoped Classical BigOperators

namespace Paper320

variable {I K : Type} [Fintype K]

theorem orBits_flip_of_witness (x : K → Bool) {i j : K}
    (hji : j ≠ i) (hj : x j = true) : orBits (flip x {i}) = orBits x := by
  have h₁ : orBits x = true := (orBits_eq_true x).mpr ⟨j, hj⟩
  have h₂ : orBits (flip x {i}) = true :=
    (orBits_eq_true _).mpr ⟨j, by rw [flip_singleton_other x hji, hj]⟩
  exact h₂.trans h₁.symm

variable [Fintype I]

theorem sensitivity_orCopies_le (f : (I → Bool) → Bool) (S₀ S₁ : ℕ)
    (h₀ : ∀ x, f x = false → sensitivityAt f x ≤ S₀)
    (h₁ : ∀ x, f x = true → sensitivityAt f x ≤ S₁) :
    sensitivity (orCopies (K := K) f) ≤ max (Fintype.card K * S₀) S₁ := by
  apply sensitivity_le
  intro x
  change sensitivityAt (compose orBits f) x ≤ _
  rw [sensitivityAt_compose]
  let y : K → Bool := fun k => f (fun a => x (k, a))
  let s : Finset K := Finset.univ.filter fun i => orBits (flip y {i}) ≠ orBits y
  change (∑ i ∈ s, sensitivityAt f (fun a => x (i, a))) ≤ _
  by_cases hy : orBits y = false
  · have hall := (orBits_eq_false y).mp hy
    calc
      _ ≤ ∑ _i ∈ s, S₀ := Finset.sum_le_sum fun i _ => h₀ _ (hall i)
      _ = s.card * S₀ := by simp
      _ ≤ Fintype.card K * S₀ := Nat.mul_le_mul_right _ (Finset.card_le_univ _)
      _ ≤ max (Fintype.card K * S₀) S₁ := le_max_left _ _
  · have htrue : orBits y = true := by cases h : orBits y <;> simp_all
    obtain ⟨i, hi⟩ := (orBits_eq_true y).mp htrue
    have hs : s ⊆ {i} := by
      intro j hj
      have hc := (Finset.mem_filter.mp hj).2
      by_contra hji
      have hij : i ≠ j := Ne.symm (by simpa only [Finset.mem_singleton] using hji)
      exact hc (orBits_flip_of_witness y hij hi)
    calc
      _ ≤ ∑ j ∈ ({i} : Finset K), sensitivityAt f (fun a => x (j, a)) :=
        Finset.sum_le_sum_of_subset_of_nonneg hs (by intros; exact Nat.zero_le _)
      _ = sensitivityAt f (fun a => x (i, a)) := by simp
      _ ≤ S₁ := h₁ _ hi
      _ ≤ max (Fintype.card K * S₀) S₁ := le_max_right _ _

end Paper320

end

end OAI

-- ---- platform node ----
open OAI OAI.Paper320
open scoped Classical BigOperators
variable {I K : Type} [Fintype K]
variable [Fintype I]

theorem solution (f : (I → Bool) → Bool) (S₀ S₁ : ℕ)
    (h₀ : ∀ x, f x = false → sensitivityAt f x ≤ S₀)
    (h₁ : ∀ x, f x = true → sensitivityAt f x ≤ S₁) :
    sensitivity (orCopies (K := K) f) ≤ max (Fintype.card K * S₀) S₁ := by
  first
    | exact OAI.Paper320.sensitivity_orCopies_le f S₀ S₁ h₀ h₁
    | exact OAI.Paper320.sensitivity_orCopies_le
    | (apply OAI.Paper320.sensitivity_orCopies_le <;> assumption)
    | (intros; apply OAI.Paper320.sensitivity_orCopies_le <;> assumption)
