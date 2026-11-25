-- Prove2me | solution 1 for NearlySubadditive.tendsto_lim
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:29:00.817121+00:00
-- url     : https://prove2.me/submissions/4c397969-6aac-4432-9d82-58ffa0503029

module
public import Mathlib.Analysis.Subadditive
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Order.MonotoneConvergence
public import Definitions.Def_Fekete_Window
public import Theorems.Thm_NearlySubadditive_tendsto_atBot_or_exists_tendsto
public import Theorems.Thm_NearlySubadditive_lim_le_div
section
@[expose] public section
noncomputable section
open Filter Set
open scoped Topology
namespace NearlySubadditive
variable {f g : ℕ → ℝ} {μ ν : ℝ} {N M : ℕ} {u v : ℕ → ℝ}
end NearlySubadditive
namespace NearlySubadditive
variable {μ : ℝ} {N : ℕ} {u : ℕ → ℝ}
private theorem le_add (h : NearlySubadditive 0 μ N u) {m n : ℕ} (hm : N ≤ m) (hmn : m ≤ n)
    (hn : (n : ℝ) ≤ μ * m) : u (m + n) ≤ u m + u n := by
  simpa using h hm hmn hn
private theorem div_add_le_max {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (h : u (m + n) ≤ u m + u n) : u (m + n) / (m + n : ℕ) ≤ max (u m / m) (u n / n) := by
  have h₁ := (div_le_iff₀' (Nat.cast_pos.2 hm)).1 (le_max_left (u m / m) (u n / n))
  have h₂ := (div_le_iff₀' (Nat.cast_pos.2 hn)).1 (le_max_right (u m / m) (u n / n))
  rw [div_le_iff₀' (Nat.cast_pos.2 (by omega)), Nat.cast_add]
  linarith
private theorem div_two_mul_le (hμ : 1 ≤ μ) (h : NearlySubadditive 0 μ N u) {n : ℕ}
    (hN : N ≤ n) : u (2 * n) / (2 * n : ℕ) ≤ u n / n := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  simpa [two_mul] using
    div_add_le_max hn hn (h.le_add hN le_rfl (le_mul_of_one_le_left n.cast_nonneg hμ))
end NearlySubadditive
end
end
end

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Filter Set
open scoped Topology
open NearlySubadditive
variable {μ : ℝ} {N : ℕ} {u : ℕ → ℝ}
namespace NearlySubadditive
theorem _root_.solution (hμ : 1 < μ) (h : NearlySubadditive 0 μ N u)
    (hbdd : BddBelow (range fun n ↦ u n / n)) :
    Tendsto (fun n ↦ u n / n) atTop (𝓝 (NearlySubadditive.lim N u)) := by
  obtain ⟨L, hL⟩ := (h.tendsto_atBot_or_exists_tendsto hμ).resolve_left
    fun hbot ↦ not_bddBelow_of_tendsto_atBot hbot hbdd
  suffices L = NearlySubadditive.lim N u by rwa [← this]
  refine le_antisymm ?_ (ge_of_tendsto hL ?_)
  · -- `L ≤ u k / k`, along the subsequence `2 ^ j * k`
    rw [NearlySubadditive.lim]
    refine le_csInf ((nonempty_Ici).image _) ?_
    rintro _ ⟨k, hk, rfl⟩
    have hk0 : 0 < k := lt_of_lt_of_le (by omega) hk
    have hNk : N ≤ k := le_of_max_le_left hk
    have hdec : ∀ j, u (2 ^ j * k) / (2 ^ j * k : ℕ) ≤ u k / k := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        refine le_trans ?_ ih
        rw [pow_succ, mul_comm (2 ^ j) 2, mul_assoc]
        exact div_two_mul_le hμ.le h (hNk.trans (Nat.le_mul_of_pos_left k (by positivity)))
    have hsub : Tendsto (fun j : ℕ ↦ 2 ^ j * k) atTop atTop :=
      tendsto_atTop_mono (fun j ↦ (Nat.lt_two_pow_self).le.trans
        (Nat.le_mul_of_pos_right _ hk0)) tendsto_id
    exact le_of_tendsto (hL.comp hsub) (Eventually.of_forall hdec)
  · -- `lim ≤ u n / n` for all large `n`
    filter_upwards [eventually_ge_atTop (max N 1)] with n hn
    exact lim_le_div hbdd (le_of_max_le_left hn) (by omega)
end NearlySubadditive
