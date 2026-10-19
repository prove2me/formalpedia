-- Prove2me | solution 1 for OAI.BackwardIntertwiners.large_curvature
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T02:41:52.349405+00:00
-- url     : https://prove2.me/submissions/3fd0cab2-f793-4729-a48a-ef7d7d0987a4

-- Generated from openai/math@1581d4c lean/OAI/Analysis/BackwardIntertwiners/ConvexEnvelope.lean:L247-L277
-- (upload_full_project.md Phase 4): solution for node OAI.BackwardIntertwiners.large_curvature. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_BackwardIntertwiners
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ConvexEnvelope

-- ---- from OAI.Analysis.BackwardIntertwiners.ConvexEnvelope ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace BackwardIntertwiners
open Filter
open scoped Topology
noncomputable section

namespace DiscreteConvex

variable {F : ℕ → ℝ}

end DiscreteConvex

namespace ConvexEnvelope

variable {I : Set ℕ} {f : ℕ → ℝ}
variable (hunbounded : ∀ n : ℕ, ∃ k, n < k ∧ k ∈ I)
variable (hne : (convexMinorants I f).Nonempty)

end ConvexEnvelope

namespace DiscreteConvex

variable {F : ℕ → ℝ}

end DiscreteConvex

lemma quadratic_upper_of_curvature {F : ℕ → ℝ} {lam : ℝ} (N : ℕ)
    (h : ∀ n, N ≤ n → F (n+2) - 2*F (n+1) + F n ≤ 2*lam) (k : ℕ) :
    F (N+k) ≤ F N + (k : ℝ) * (F (N+1) - F N) + lam * k * (k-1) := by
  have hs (k : ℕ) : F (N+k+1) - F (N+k) ≤
      F (N+1) - F N + 2*lam*k := by
    induction k with
    | zero => simp
    | succ k ih =>
      have hh := h (N+k) (Nat.le_add_right _ _)
      have e₁ : N + (k+1) + 1 = N+k+2 := by omega
      have e₂ : N + (k+1) = N+k+1 := by omega
      rw [e₁, e₂]
      push_cast
      linarith
  induction k with
  | zero => simp
  | succ k ih =>
    have hh := hs k
    have e : N + (k+1) = N+k+1 := by omega
    rw [e]
    push_cast
    nlinarith

lemma large_curvature {F : ℕ → ℝ} {lam μ : ℝ} (hμ : 0 < μ) (hlamμ : lam < μ)
    (hq : ∀ᶠ n : ℕ in atTop, μ * (n : ℝ)^2 ≤ F n) :
    ∀ N : ℕ, ∃ n, N ≤ n ∧ 2*lam < F (n+2) - 2*F (n+1) + F n := by
  intro N
  by_contra! h
  obtain ⟨Q, hQ⟩ := eventually_atTop.1 hq
  let C := |F (N+1) - F N - lam| + |F N|
  obtain ⟨k, hk⟩ := exists_nat_gt (max (max (Q : ℝ) 1) (C / (μ-lam)))
  have hkQ : (Q : ℝ) < k := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_left _ _)) hk
  have hk1 : (1 : ℝ) < k := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_left _ _)) hk
  have hkC : C / (μ-lam) < k := lt_of_le_of_lt (le_max_right _ _) hk
  have hk0 : (0 : ℝ) < k := lt_trans zero_lt_one hk1
  have hQN : Q ≤ N+k := by exact Nat.le_trans (Nat.le_of_lt (Nat.cast_lt.mp hkQ)) (Nat.le_add_left _ _)
  have hlo := hQ (N+k) hQN
  have hhi := quadratic_upper_of_curvature N h k
  have hNC : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hlow : μ * (k : ℝ)^2 ≤ F (N+k) := by
    push_cast at hlo
    calc μ * (k : ℝ)^2 ≤ μ * ((N : ℝ) + k)^2 := by gcongr; linarith
         _ ≤ F (N+k) := hlo
  have hF0 : F N ≤ |F N| * k := calc
    F N ≤ |F N| := le_abs_self _
    _ ≤ |F N| * k := le_mul_of_one_le_right (abs_nonneg _) hk1.le
  have hF1 : (F (N+1) - F N - lam) * k ≤ |F (N+1) - F N - lam| * k :=
    mul_le_mul_of_nonneg_right (le_abs_self _) hk0.le
  have hup : F (N+k) ≤ lam * (k : ℝ)^2 + C*k := by
    dsimp [C]
    nlinarith [hhi]
  have hlarge : C < (k : ℝ) * (μ-lam) := (div_lt_iff₀ (sub_pos.mpr hlamμ)).mp hkC
  have hstrict := mul_lt_mul_of_pos_right hlarge hk0
  nlinarith

namespace DiscreteConvex

variable {F : ℕ → ℝ}

end DiscreteConvex

namespace DiscreteConvex

variable {F : ℕ → ℝ}

end DiscreteConvex

end
end BackwardIntertwiners

end OAI

-- ---- platform node ----
open OAI OAI.BackwardIntertwiners
open Filter
open scoped Topology


theorem solution : type_of% @_root_.OAI.BackwardIntertwiners.large_curvature := @_root_.OAI.BackwardIntertwiners.large_curvature
