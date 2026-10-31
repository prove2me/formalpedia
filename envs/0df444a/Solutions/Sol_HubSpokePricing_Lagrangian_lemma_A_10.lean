-- Prove2me | solution 1 for HubSpokePricing.Lagrangian.lemma_A_10
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T19:18:24.97979+00:00
-- url     : https://prove2.me/submissions/9e1aa1d6-232a-4f52-9b35-fa44a6e18eb2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_HubSpokePricing_Lagrangian_Model
import Theorems.Thm_HubSpokePricing_Lagrangian_proposition_3_3
import Theorems.Thm_HubSpokePricing_Lagrangian_lemma_B_1_support

namespace HubSpokeA10Aux

open HubSpokePricing.Lagrangian Finset

lemma rev_diff (rbar omega : ℝ) (r : ℝ → ℝ) (hr : RevenueAssumption rbar omega r) (u v : ℝ)
    (hu : u ∈ Set.Icc (0 : ℝ) 1) (hv : v ∈ Set.Icc (0 : ℝ) 1) : r u - r v ≤ omega * |u - v| := by
  obtain ⟨-, -, -, hd, hb, -⟩ := hr
  have := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_derivWithin_le hd
    (fun x hx => by rw [Real.norm_eq_abs]; exact hb x hx) hv hu
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at this
  exact (le_abs_self _).trans this

end HubSpokeA10Aux

open HubSpokePricing.Lagrangian Finset HubSpokeA10Aux

theorem solution (N : Network) (hN : N.Standing) (lam : ℝ) (hlam : 0 ≤ lam)
    (i : Fin N.n) (s : SpokeSol N.m) (hs : SpokeOptimal N lam i s)
    (t x : ℕ) (hx1 : 1 ≤ x) (hxm : x ≤ N.m) :
    spokeValue N i s t x - spokeValue N i s t (x - 1) ≤ N.omega := by
  obtain ⟨hsupp, -⟩ := lemma_B_1_support N hN lam hlam i s hs
  have hmono := proposition_3_3 N hN lam hlam i s hs
  obtain ⟨hp0, -, hdo, hdi, -, hdo0, hdil⟩ := hs.1
  obtain ⟨-, hqo, hqi, hqsum, -, hom, hr⟩ := hN
  have hqo' := hqo i
  have hqi' := hqi i
  have hq1 : N.qOut i + N.qIn i ≤ 1 := by
    rw [← hqsum]
    exact single_le_sum (f := fun j => N.qOut j + N.qIn j)
      (fun j _ => by linarith [hqo j, hqi j]) (mem_univ i)
  -- the Lagrangian controls as functions of the level
  set lo : ℕ → ℝ := lagOut s with hlo
  set li : ℕ → ℝ := lagIn s with hli
  have hdoN : ∀ y, 0 ≤ s.dOutN y ∧ s.dOutN y ≤ 1 := by
    intro y; unfold SpokeSol.dOutN; split_ifs
    · exact hdo _
    · exact ⟨le_rfl, zero_le_one⟩
  have hdiN : ∀ y, 0 ≤ s.dInN y ∧ s.dInN y ≤ 1 := by
    intro y; unfold SpokeSol.dInN; split_ifs
    · exact hdi _
    · exact ⟨le_rfl, zero_le_one⟩
  have hlo01 : ∀ y, lo y ∈ Set.Icc (0 : ℝ) 1 := by
    intro y; simp only [hlo, lagOut]; split_ifs
    · exact hdoN y
    · exact ⟨zero_le_one, le_rfl⟩
  have hli01 : ∀ y, li y ∈ Set.Icc (0 : ℝ) 1 := by
    intro y; simp only [hli, lagIn]; split_ifs
    · exact hdiN y
    · exact ⟨le_rfl, zero_le_one⟩
  have hlo0 : lo 0 = 0 := by
    simp only [hlo, lagOut, Nat.zero_le, if_true, SpokeSol.dOutN, dif_pos]
    exact hdo0
  have hlim : li N.m = 0 := by
    simp only [hli, lagIn]
    split_ifs
    · unfold SpokeSol.dInN; rw [dif_pos le_rfl]; exact hdil
    · rfl
  -- positivity on `[0 : top]`
  have hpos : ∀ y (hy : y ≤ N.m), y ≤ s.top → 0 < s.p ⟨y, by omega⟩ :=
    fun y hy hyt => (hsupp ⟨y, by omega⟩).2 hyt
  -- monotonicity of the controls on `[0 : m]`
  have hmon : ∀ y, 1 ≤ y → y ≤ N.m → lo (y - 1) ≤ lo y ∧ li y ≤ li (y - 1) := by
    intro y hy1 hym
    simp only [hlo, hli, lagOut, lagIn]
    by_cases hyt : y ≤ s.top
    · have h1 : y - 1 ≤ s.top := by omega
      rw [if_pos hyt, if_pos h1, if_pos hyt, if_pos h1]
      have m := hmono ⟨y - 1, by omega⟩ ⟨y, by omega⟩ (by simp only [Fin.mk_le_mk]; omega)
        (hpos _ (by omega) h1) (hpos _ hym hyt)
      simp only [SpokeSol.dOutN, SpokeSol.dInN, dif_pos (show y - 1 ≤ N.m by omega), dif_pos hym]
      exact m
    · rw [if_neg hyt, if_neg hyt]
      by_cases h1 : y - 1 ≤ s.top
      · rw [if_pos h1, if_pos h1]
        exact ⟨(hdoN _).2, (hdiN _).1⟩
      · rw [if_neg h1, if_neg h1]
        exact ⟨le_rfl, le_rfl⟩
  clear hpos
  -- induction on the horizon
  induction t generalizing x with
  | zero => simp [spokeValue]; exact hom.le
  | succ t ih =>
    set V := spokeValue N i s t with hV
    have hx' : x - 1 + 1 = x := by omega
    have hstep : spokeValue N i s (t + 1) x - spokeValue N i s (t + 1) (x - 1) =
        N.qOut i * (N.rOut i (lo x) - N.rOut i (lo (x - 1))) +
        N.qIn i * (N.rIn i (li x) - N.rIn i (li (x - 1))) +
        N.qIn i * li x * (V (x + 1) - V x) +
        N.qOut i * lo (x - 1) * (V (x - 1) - V (x - 1 - 1)) +
        (1 - N.qOut i * lo x - N.qIn i * li (x - 1)) * (V x - V (x - 1)) := by
      simp only [spokeValue, hV, hlo, hli, hx']
      ring
    rw [hstep]
    obtain ⟨mo1, mo2⟩ := hmon x hx1 hxm
    have hO := rev_diff _ _ _ (hr i).1 (lo x) (lo (x - 1)) (hlo01 x) (hlo01 (x - 1))
    have hI := rev_diff _ _ _ (hr i).2 (li x) (li (x - 1)) (hli01 x) (hli01 (x - 1))
    rw [abs_of_nonneg (by linarith)] at hO
    rw [abs_of_nonpos (by linarith)] at hI
    -- the three continuation-value differences
    have hDx := ih x hx1 hxm
    have hD1 : N.qIn i * li x * (V (x + 1) - V x) ≤ N.qIn i * li x * N.omega := by
      by_cases hxm' : x + 1 ≤ N.m
      · have := ih (x + 1) (by omega) hxm'
        simp only [Nat.add_sub_cancel] at this
        exact mul_le_mul_of_nonneg_left this (mul_nonneg hqi'.le (hli01 x).1)
      · have : x = N.m := by omega
        rw [this, hlim]; simp
    have hD0 : N.qOut i * lo (x - 1) * (V (x - 1) - V (x - 1 - 1)) ≤
        N.qOut i * lo (x - 1) * N.omega := by
      by_cases hx2 : 2 ≤ x
      · have := ih (x - 1) (by omega) (by omega)
        exact mul_le_mul_of_nonneg_left this (mul_nonneg hqo'.le (hlo01 _).1)
      · have : x - 1 = 0 := by omega
        rw [this, hlo0]; simp
    have hK : 0 ≤ 1 - N.qOut i * lo x - N.qIn i * li (x - 1) := by
      have := mul_le_mul_of_nonneg_left (hlo01 x).2 hqo'.le
      have := mul_le_mul_of_nonneg_left (hli01 (x - 1)).2 hqi'.le
      linarith
    have hKD := mul_le_mul_of_nonneg_left hDx hK
    have hO' := mul_le_mul_of_nonneg_left hO hqo'.le
    have hI' := mul_le_mul_of_nonneg_left hI hqi'.le
    nlinarith
