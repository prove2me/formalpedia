-- Prove2me | solution 1 for NearlySubadditive.tendsto_atBot_or_exists_tendsto_of_summable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:28:36.073702+00:00
-- url     : https://prove2.me/submissions/f1cd7304-a61b-4ba9-9ccf-a275c51808eb

module
public import Definitions.Def_Fekete_Window
public import Mathlib.Analysis.PSeries
public import Definitions.Def_Fekete_DeBruijnErdos
public import Theorems.Thm_sub_le_sum_Ico_inv_sq
public import Theorems.Thm_NearlySubadditive_mono
public import Theorems.Thm_NearlySubadditive_tendsto_atBot_or_exists_tendsto

section
@[expose] public section
noncomputable section
open Filter Finset
open scoped Topology
section Telescoping
variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]
end Telescoping
namespace NearlySubadditive
variable {f u : ℕ → ℝ} {μ : ℝ} {N : ℕ}
private theorem summable_corr (hfs : Summable fun n : ℕ ↦ f n / (n : ℝ) ^ 2) {c : ℕ}
    (hc : 0 < c) : Summable (corr f c) := by
  have h := (hfs.comp_injective (mul_right_injective₀ hc.ne')).mul_left ((c : ℝ) ^ 2)
  refine h.congr fun x ↦ ?_
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp [corr]
  have hx' : (x : ℝ) ≠ 0 := by positivity
  have hc' : (c : ℝ) ≠ 0 := by positivity
  simp only [Function.comp_apply, corr, Nat.cast_mul]
  field_simp
private theorem le_sum_corr (hf0 : 0 ≤ f) (hf : Monotone f) {c m n p : ℕ} (hm : 0 < m)
    (hp : p ≤ c * m) :
    f p * (1 / m - 1 / (m + n : ℕ)) ≤ ∑ k ∈ range n, corr f c (k + m) := by
  have := sub_le_sum_Ico_inv_sq (α := ℝ) hm.ne' (Nat.le_add_right m n)
  rw [sum_Ico_eq_sum_range, Nat.add_sub_cancel_left] at this
  rw [one_div, one_div]
  refine (mul_le_mul_of_nonneg_left this (hf0 p)).trans ?_
  rw [mul_sum]
  refine sum_le_sum fun k _ ↦ ?_
  rw [corr, ← div_eq_mul_inv, add_comm k m]
  exact div_le_div_of_nonneg_right (hf (hp.trans (Nat.mul_le_mul_left c (by omega))))
    (sq_nonneg _)
end NearlySubadditive
end
end
end

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Filter Finset
open scoped Topology
open NearlySubadditive
variable {f u : ℕ → ℝ} {μ : ℝ} {N : ℕ}
namespace NearlySubadditive
theorem _root_.solution (hμ : 1 < μ) (h : NearlySubadditive f μ N u)
    (hf : Monotone f) (hfs : Summable fun n : ℕ ↦ f n / (n : ℝ) ^ 2) :
    Tendsto (fun n ↦ u n / n) atTop atBot ∨ ∃ L, Tendsto (fun n ↦ u n / n) atTop (𝓝 L) := by
  -- replacing `f` by `max f 0`, we may assume `f ≥ 0`
  wlog hf0 : 0 ≤ f generalizing f
  · refine this (h.mono (fun n ↦ le_max_left (f n) 0) le_rfl le_rfl)
      (fun a b hab ↦ max_le_max (hf hab) le_rfl)
      (hfs.abs.of_nonneg_of_le (fun n ↦ div_nonneg (le_max_right _ _) (sq_nonneg _)) fun n ↦ ?_)
      fun n ↦ le_max_right _ _
    rw [abs_div, abs_of_nonneg (sq_nonneg (n : ℝ))]
    exact div_le_div_of_nonneg_right (max_le (le_abs_self _) (abs_nonneg _)) (sq_nonneg _)
  set c : ℕ := ⌈1 + μ⌉₊
  have hc : (1 + μ : ℝ) ≤ c := Nat.le_ceil _
  have hc0 : 0 < c := by exact_mod_cast (show (0 : ℝ) < c by linarith)
  have hcs := summable_corr hfs hc0
  set T : ℕ → ℝ := fun n ↦ ∑' k, corr f c (k + n)
  have hT : Tendsto T atTop (𝓝 0) := tendsto_sum_nat_add (corr f c)
  -- splitting off a block of the tail
  have hsplit : ∀ m n, T m = ∑ k ∈ range n, corr f c (k + m) + T (m + n) := fun m n ↦ by
    have := ((summable_nat_add_iff m).2 hcs).sum_add_tsum_nat_add n
    simp only [T] at this ⊢
    rw [← this]
    congr 1
    exact tsum_congr fun k ↦ by rw [add_assoc, add_comm n m]
  -- the corrected sequence is subadditive on the window
  set G : ℕ → ℝ := fun n ↦ u n + n * T n
  have hG : NearlySubadditive 0 μ (max N 1) G := by
    intro m n hm hmn hnm
    have hmR : (0 : ℝ) < m := Nat.cast_pos.2 (by omega)
    have hnR : (0 : ℝ) < n := Nat.cast_pos.2 (by omega)
    have hmnR : (m : ℝ) ≤ n := by exact_mod_cast hmn
    have hcm := mul_le_mul_of_nonneg_right hc hmR.le
    have hcn := mul_le_mul_of_nonneg_right hc hnR.le
    have hμn := le_mul_of_one_le_left hnR.le hμ.le
    have hp₁ : m + n ≤ c * m := by
      exact_mod_cast (show ((m + n : ℕ) : ℝ) ≤ c * m by push_cast; linarith)
    have hp₂ : m + n ≤ c * n := by
      exact_mod_cast (show ((m + n : ℕ) : ℝ) ≤ c * n by push_cast; linarith)
    have h1 := mul_le_mul_of_nonneg_left (le_sum_corr (n := n) hf0 hf (by omega) hp₁) hmR.le
    have h2 := mul_le_mul_of_nonneg_left (le_sum_corr (n := m) hf0 hf (by omega) hp₂) hnR.le
    have key : (m : ℝ) * (f (m + n) * (1 / m - 1 / (m + n))) +
        n * (f (m + n) * (1 / n - 1 / (n + m))) = f (m + n) := by
      field_simp; ring
    push_cast at h1 h2
    simp only [G, Pi.zero_apply, add_zero]
    push_cast
    rw [hsplit m n, hsplit n m, add_comm n m]
    linarith [h (le_of_max_le_left hm) hmn hnm]
  -- transfer the conclusion from `G` back to `u`
  have hGu : (fun n ↦ u n / n) =ᶠ[atTop] fun n ↦ G n / n - T n := by
    filter_upwards [eventually_ne_atTop 0] with n hn
    have : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    simp only [G]
    field_simp
    ring
  rcases hG.tendsto_atBot_or_exists_tendsto hμ with hbot | ⟨L, hL⟩
  · refine Or.inl (Tendsto.congr' hGu.symm ?_)
    simpa [sub_eq_add_neg] using hbot.atBot_add hT.neg
  · exact Or.inr ⟨L, Tendsto.congr' hGu.symm (by simpa using hL.sub hT)⟩
end NearlySubadditive
