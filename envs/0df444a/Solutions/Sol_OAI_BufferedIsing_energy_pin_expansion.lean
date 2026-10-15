-- Prove2me | solution 1 for OAI.BufferedIsing.energy_pin_expansion
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T22:42:29.58284+00:00
-- url     : https://prove2.me/submissions/c759c719-2732-4ace-b49f-0fe29ac50de0

-- Generated from openai/math@1581d4c lean/OAI/Probability/Ising/PinnedMarginal.lean:L165-L222
-- (upload_full_project.md Phase 4): solution for node OAI.BufferedIsing.energy_pin_expansion. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_BufferedIsing
import Definitions.Def_OAI_Probability_Ising_Basic
import Definitions.Def_OAI_Probability_Ising_Colorings
import Definitions.Def_OAI_Probability_Ising_EdwardsSokal
import Definitions.Def_OAI_Probability_Ising_TwoSpin
import Definitions.Def_OAI_Probability_Ising_SpinCorrelation
import Definitions.Def_OAI_Probability_Ising_Marginals
import Definitions.Def_OAI_Probability_Ising_PinnedMarginal

-- ---- from OAI.Probability.Ising.PinnedMarginal ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open scoped BigOperators Classical

namespace BufferedIsing

lemma sum_pin_incidence {n m : ℕ} (l r : Fin m → Fin n) (F : Finset (Fin n)) (f : Fin m → ℝ) (σ : Fin n → ℝ) :
    (∑ v : Fin n, if v ∉ F then (∑ e, if l e = v ∧ r e ∈ F then f e else 0) * σ v else 0) =
      ∑ e, if l e ∉ F ∧ r e ∈ F then f e * σ (l e) else 0 := by
  classical
  calc
    _ = ∑ v : Fin n, ∑ e, if v ∉ F ∧ l e = v ∧ r e ∈ F then f e * σ v else 0 := by
      apply Finset.sum_congr rfl
      intro v _
      by_cases hv : v ∈ F
      · simp [hv]
      · simp only [hv, not_false_eq_true, ite_true, true_and, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro e _
        split_ifs <;> simp
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e _
      have H : ∀ v : Fin n, (v ∉ F ∧ l e = v ∧ r e ∈ F) ↔
          (l e = v ∧ l e ∉ F ∧ r e ∈ F) := by
        intro v
        constructor
        · rintro ⟨hv, he, hr⟩
          exact ⟨he, he.symm ▸ hv, hr⟩
        · rintro ⟨he, hl, hr⟩
          exact ⟨he ▸ hl, he, hr⟩
      simp_rw [H]
      by_cases he : l e ∉ F ∧ r e ∈ F
      · simp [he]
      · simp [he]

lemma energy_pin_expansion {n m : ℕ} (G : FiniteGraph n m)
    (h : Fin n → ℝ) (F : Finset (Fin n)) (τ ρ : Spins n) (hρ : AgreesOn F ρ τ) :
    energy G h ρ = pinConstant G h F τ +
      (∑ e, if G.left e ∉ F ∧ G.right e ∉ F then
        G.coupling e * spin (ρ (G.left e)) * spin (ρ (G.right e)) else 0) +
      ∑ v : Fin n, if v ∉ F then
        (h v + (∑ e, if G.left e = v ∧ G.right e ∈ F then
          G.coupling e * spin (τ (G.right e)) else 0) +
          ∑ e, if G.right e = v ∧ G.left e ∈ F then
            G.coupling e * spin (τ (G.left e)) else 0) * spin (ρ v) else 0 := by
  classical
  have hsplit : (∑ v : Fin n, if v ∉ F then
        (h v + (∑ e, if G.left e = v ∧ G.right e ∈ F then
          G.coupling e * spin (τ (G.right e)) else 0) +
          ∑ e, if G.right e = v ∧ G.left e ∈ F then
            G.coupling e * spin (τ (G.left e)) else 0) * spin (ρ v) else 0) =
      (∑ v : Fin n, if v ∉ F then h v * spin (ρ v) else 0) +
      (∑ e, if G.left e ∉ F ∧ G.right e ∈ F then
        (G.coupling e * spin (τ (G.right e))) * spin (ρ (G.left e)) else 0) +
      (∑ e, if G.right e ∉ F ∧ G.left e ∈ F then
        (G.coupling e * spin (τ (G.left e))) * spin (ρ (G.right e)) else 0) := by
    rw [← sum_pin_incidence G.left G.right F
      (fun e => G.coupling e * spin (τ (G.right e))) (fun v => spin (ρ v)),
      ← sum_pin_incidence G.right G.left F
        (fun e => G.coupling e * spin (τ (G.left e))) (fun v => spin (ρ v))]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v _
    by_cases hv : v ∈ F <;> simp [hv, add_mul]
  rw [hsplit]
  unfold energy pinConstant
  have he : (∑ e, G.coupling e * spin (ρ (G.left e)) * spin (ρ (G.right e))) =
      (∑ e, if G.left e ∈ F ∧ G.right e ∈ F then
        G.coupling e * spin (τ (G.left e)) * spin (τ (G.right e)) else 0) +
      (∑ e, if G.left e ∉ F ∧ G.right e ∉ F then
        G.coupling e * spin (ρ (G.left e)) * spin (ρ (G.right e)) else 0) +
      (∑ e, if G.left e ∉ F ∧ G.right e ∈ F then
        (G.coupling e * spin (τ (G.right e))) * spin (ρ (G.left e)) else 0) +
      (∑ e, if G.right e ∉ F ∧ G.left e ∈ F then
        (G.coupling e * spin (τ (G.left e))) * spin (ρ (G.right e)) else 0) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e _
    by_cases hl : G.left e ∈ F <;> by_cases hr : G.right e ∈ F
    · simp [hl, hr, hρ _ hl, hρ _ hr]
    · simp [hl, hr, hρ _ hl]
    · simp [hl, hr, hρ _ hr, mul_comm, mul_left_comm]
    · simp [hl, hr]
  have hv : (∑ v, h v * spin (ρ v)) =
      (∑ v ∈ F, h v * spin (τ v)) +
      (∑ v : Fin n, if v ∉ F then h v * spin (ρ v) else 0) := by
    rw [← Fintype.sum_extend_by_zero F (fun v => h v * spin (τ v)),
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v _
    by_cases hv : v ∈ F <;> simp [hv, hρ v]
  rw [he, hv]
  ring

end BufferedIsing

end OAI

-- ---- platform node ----
open OAI OAI.BufferedIsing
open scoped BigOperators Classical

theorem solution {n m : ℕ} (G : FiniteGraph n m)
    (h : Fin n → ℝ) (F : Finset (Fin n)) (τ ρ : Spins n) (hρ : AgreesOn F ρ τ) :
    energy G h ρ = pinConstant G h F τ +
      (∑ e, if G.left e ∉ F ∧ G.right e ∉ F then
        G.coupling e * spin (ρ (G.left e)) * spin (ρ (G.right e)) else 0) +
      ∑ v : Fin n, if v ∉ F then
        (h v + (∑ e, if G.left e = v ∧ G.right e ∈ F then
          G.coupling e * spin (τ (G.right e)) else 0) +
          ∑ e, if G.right e = v ∧ G.left e ∈ F then
            G.coupling e * spin (τ (G.left e)) else 0) * spin (ρ v) else 0 := by
  first
    | exact OAI.BufferedIsing.energy_pin_expansion G h F τ ρ hρ
    | exact OAI.BufferedIsing.energy_pin_expansion
    | (apply OAI.BufferedIsing.energy_pin_expansion <;> assumption)
    | (intros; apply OAI.BufferedIsing.energy_pin_expansion <;> assumption)
