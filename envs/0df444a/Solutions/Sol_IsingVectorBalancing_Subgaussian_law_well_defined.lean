-- Prove2me | solution 1 for IsingVectorBalancing.Subgaussian.law_well_defined
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T17:25:57.646771+00:00
-- url     : https://prove2.me/submissions/7317505d-7aca-4c94-ba66-af9f24135c7b

import Mathlib
import Definitions.Def_IsingVectorBalancing_Subgaussian_Law

section
set_option autoImplicit false
open scoped BigOperators
namespace IsingVectorBalancing.Subgaussian.Dev.LW
open IsingVectorBalancing.Subgaussian

theorem spin_cases (b : Bool) : spin b = 1 ∨ spin b = -1 := by
  cases b <;> simp [spin]

theorem abs_inner_le {d : ℕ} {x y : Vec d} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    |inner ℝ x y| ≤ 1 :=
  (abs_real_inner_le_norm x y).trans (mul_le_one₀ hx (norm_nonneg _) hy)

theorem factor_nonneg {d : ℕ} {x y : Vec d} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) (a b : Bool) :
    0 ≤ 1 - spin a * spin b * inner ℝ x y := by
  have := abs_inner_le hx hy
  rw [abs_le] at this
  rcases spin_cases a with ha | ha <;> rcases spin_cases b with hb | hb <;> rw [ha, hb] <;>
    nlinarith [this.1, this.2]

theorem pu_of_inner {d : ℕ} {x y : Vec d} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1)
    (h : inner ℝ x y = 1 ∨ inner ℝ x y = -1) : ParallelUnit x y := by
  have habs : |inner ℝ x y| = 1 := by rcases h with h | h <;> simp [h]
  have h1 : 1 ≤ ‖x‖ * ‖y‖ := habs ▸ abs_real_inner_le_norm x y
  have hnx : ‖x‖ = 1 := by
    by_contra hne
    have : ‖x‖ < 1 := lt_of_le_of_ne hx hne
    nlinarith [norm_nonneg y, norm_nonneg x]
  have hny : ‖y‖ = 1 := by
    by_contra hne
    have : ‖y‖ < 1 := lt_of_le_of_ne hy hne
    nlinarith [norm_nonneg y, norm_nonneg x]
  refine ⟨hnx, hny, ?_⟩
  rcases h with h | h
  · left
    have := (inner_eq_norm_mul_iff_real (x := x) (y := y)).mp (by rw [h, hnx, hny]; norm_num)
    rw [hnx, hny] at this; simpa using this
  · right
    have := (inner_eq_norm_mul_iff_real (x := x) (y := -y)).mp (by
      rw [inner_neg_right, h, hnx, norm_neg, hny]; norm_num)
    rw [hnx, norm_neg, hny] at this; simpa using this

theorem inner_of_pu {d : ℕ} {x y : Vec d} (h : ParallelUnit x y) :
    inner ℝ x y = 1 ∨ inner ℝ x y = -1 := by
  obtain ⟨hx, hy, h | h⟩ := h
  · left; subst h; rw [real_inner_self_eq_norm_sq, hx]; norm_num
  · right; subst h; rw [inner_neg_left, real_inner_self_eq_norm_sq, (norm_neg y ▸ hx : ‖y‖ = 1)]; norm_num

theorem pu_symm {d : ℕ} {x y : Vec d} (h : ParallelUnit x y) : ParallelUnit y x := by
  obtain ⟨hx, hy, h | h⟩ := h
  · exact ⟨hy, hx, Or.inl h.symm⟩
  · exact ⟨hy, hx, Or.inr (by rw [h]; simp)⟩

open Classical in
noncomputable def sig {n d : ℕ} (v : Fin n → Vec d) : Configuration n := fun i =>
  if h : ∃ j : Fin n, j < i ∧ ParallelUnit (v i) (v j) then
    decide (inner ℝ (v i) (v (Classical.choose h)) < 0)
  else true

theorem weight_sig_pos {n d : ℕ} {v : Fin n → Vec d} (hv : Admissible v) :
    0 < weight v (sig v) := by
  unfold weight
  refine Finset.prod_pos fun i _ => Finset.prod_pos fun j hj => ?_
  have hij : i < j := (Finset.mem_filter.mp hj).2
  refine lt_of_le_of_ne (factor_nonneg (hv.1 i) (hv.1 j) _ _) (fun h0 => ?_)
  have h1 : spin (sig v i) * spin (sig v j) * inner ℝ (v i) (v j) = 1 := by linarith
  have hpm : inner ℝ (v i) (v j) = 1 ∨ inner ℝ (v i) (v j) = -1 := by
    have hs := spin_cases (sig v i)
    have hs' := spin_cases (sig v j)
    rcases hs with ha | ha <;> rcases hs' with hb | hb <;> rw [ha, hb] at h1 <;>
      [left; right; right; left] <;> linarith
  have hpu : ParallelUnit (v i) (v j) := pu_of_inner (hv.1 i) (hv.1 j) hpm
  have hpu' : ParallelUnit (v j) (v i) := pu_symm hpu
  -- j has a smaller partner
  have hex : ∃ k : Fin n, k < j ∧ ParallelUnit (v j) (v k) := ⟨i, hij, hpu'⟩
  -- i has no smaller partner
  have hnoi : ¬ ∃ k : Fin n, k < i ∧ ParallelUnit (v i) (v k) := by
    rintro ⟨k, hk, hpk⟩
    exact hv.2 i j k hij.ne (hk.ne') (hk.trans hij).ne' ⟨hpu, hpk⟩
  have hsi : sig v i = true := by simp [sig, hnoi]
  have hch : Classical.choose hex = i := by
    have hspec := Classical.choose_spec hex
    by_contra hne
    exact hv.2 j i (Classical.choose hex) hij.ne' (Ne.symm (hspec.1.ne)) (Ne.symm hne)
      ⟨hpu', hspec.2⟩
  have hsj : sig v j = decide (inner ℝ (v j) (v i) < 0) := by
    simp only [sig, dif_pos hex]
    rw [hch]
  rw [hsi, hsj, real_inner_comm] at h1
  rcases inner_of_pu hpu with hp | hp <;> rw [hp] at h1 <;> simp [spin] at h1 <;> norm_num at h1

end IsingVectorBalancing.Subgaussian.Dev.LW

namespace IsingVectorBalancing.Subgaussian
open IsingVectorBalancing.Subgaussian.Dev.LW in
theorem chk_law_well_defined {n d : ℕ} (v : Fin n → Vec d) (hv : Admissible v)
    (h : Fin n → ℝ) :
    (∀ σ : Configuration n, 0 ≤ tiltedWeight v h σ) ∧
    0 < partition v h ∧
    (∀ σ : Configuration n, 0 ≤ probability v h σ) ∧
    (∑ σ : Configuration n, probability v h σ) = 1 := by
  have hw : ∀ σ : Configuration n, 0 ≤ weight v σ := fun σ =>
    Finset.prod_nonneg fun i _ => Finset.prod_nonneg fun j _ => factor_nonneg (hv.1 i) (hv.1 j) _ _
  have ht : ∀ σ : Configuration n, 0 ≤ tiltedWeight v h σ := fun σ =>
    mul_nonneg (Real.exp_pos _).le (hw σ)
  have hZ : 0 < partition v h := by
    unfold partition
    refine lt_of_lt_of_le ?_ (Finset.single_le_sum (fun σ _ => ht σ) (Finset.mem_univ (sig v)))
    exact mul_pos (Real.exp_pos _) (weight_sig_pos hv)
  refine ⟨ht, hZ, fun σ => div_nonneg (ht σ) hZ.le, ?_⟩
  unfold probability
  rw [← Finset.sum_div]
  exact div_self hZ.ne'

end IsingVectorBalancing.Subgaussian
end

theorem solution : type_of% @IsingVectorBalancing.Subgaussian.chk_law_well_defined := @IsingVectorBalancing.Subgaussian.chk_law_well_defined
