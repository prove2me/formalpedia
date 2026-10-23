-- Prove2me | solution 2 for NeedPersuasion.FullInfo.proposition_3
-- status  : ACCEPTED   (disprove)
-- author  : @tianyipeng
-- created : 2026-10-22T23:29:50.464014+00:00
-- url     : https://prove2.me/submissions/4dc795a0-ffaa-45af-b5a8-413ac5438e74

import Mathlib
import Definitions.Def_NeedPersuasion_FullInfo_Model
import Definitions.Def_NeedPersuasion_FullInfo_Constants

namespace NP3Aux
open NeedPersuasion.FullInfo

/-- Linear lower bound on a concave-type decreasing utility. -/
lemma uL_lower (u : ℕ → ℝ) (hd : Antitone (fun n => u n - u (n + 1))) (i : ℕ) :
    u 0 - i * (u 0 - u 1) ≤ u i := by
  induction i with
  | zero => simp
  | succ i ih =>
    have := hd (Nat.zero_le i)
    simp only at this
    push_cast
    linarith

lemma summable_geom_mul_concave (u : ℕ → ℝ) (hd : Antitone (fun n => u n - u (n + 1)))
    (ha : StrictAnti u) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun j : ℕ => r ^ j * u j) := by
  have hb : Summable (fun j : ℕ => r ^ j * (|u 0| + j * (u 0 - u 1))) := by
    have h1 : Summable (fun j : ℕ => r ^ j) := summable_geometric_of_lt_one hr0 hr1
    have h2 : Summable (fun j : ℕ => (j : ℝ) ^ 1 * r ^ j) :=
      summable_pow_mul_geometric_of_norm_lt_one 1 (by rw [Real.norm_eq_abs, abs_of_nonneg hr0]; exact hr1)
    have := (h1.mul_left (|u 0|)).add (h2.mul_left (u 0 - u 1))
    refine this.congr ?_
    intro j; ring
  refine Summable.of_norm_bounded hb ?_
  intro j
  have hd1 : 0 ≤ u 0 - u 1 := by have := ha (Nat.zero_lt_one); linarith
  have hlo := uL_lower u hd j
  have hhi : u j ≤ u 0 := ha.antitone (Nat.zero_le j)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hr0 j)]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hr0 j)
  rw [abs_le]
  constructor
  · have : -|u 0| ≤ u 0 := neg_abs_le _
    nlinarith
  · have := le_abs_self (u 0)
    have : 0 ≤ (j : ℝ) * (u 0 - u 1) := mul_nonneg (Nat.cast_nonneg _) hd1
    linarith

/-- Threshold policies at integer thresholds are admission policies. -/
lemma threshold_mem_PiAP (M : Model) (hM : M.Standing) (hH0 : 0 < M.lamH) (hH1 : M.lamH < 1)
    (hFin : Summable (fun n : ℕ => M.lamH ^ n * M.uH n)) (n : ℕ) :
    thresholdPolicy M (n : ℝ) ∈ PiAP M := by
  obtain ⟨hL, -, hlam, -, -, -, -, haL, haH, hdL⟩ := hM
  set w : ℕ → ℝ := fun k => if k ≤ n then M.lam ^ k else M.lam ^ n * M.lamH * M.lamH ^ (k - n - 1)
    with hw
  have hpol : thresholdPolicy M (n : ℝ) = fun k => w k / ∑' j, w j := by
    funext k
    simp [thresholdPolicy, hw, Nat.floor_natCast, Int.fract_natCast]
  have hlam0 : 0 < M.lam := by unfold Model.lam; linarith
  have hHl : M.lamH ≤ M.lam := by unfold Model.lam; linarith
  have hw0 : ∀ k, 0 ≤ w k := by
    intro k; simp only [hw]; split_ifs <;> positivity
  have hshift : ∀ j, w (j + (n + 1)) = M.lam ^ n * M.lamH * M.lamH ^ j := by
    intro j; simp only [hw]; rw [if_neg (by omega)]; congr 2; omega
  have hsum : Summable w := by
    rw [← summable_nat_add_iff (n + 1)]
    have := (summable_geometric_of_lt_one hH0.le hH1).mul_left (M.lam ^ n * M.lamH)
    exact this.congr (fun j => (hshift j).symm)
  have hS : 0 < ∑' j, w j := by
    have := hsum.le_tsum 0 (fun j _ => hw0 j)
    have h0 : w 0 = 1 := by simp [hw]
    linarith
  rw [hpol]
  refine ⟨fun k => div_nonneg (hw0 k) hS.le, ?_, ?_, ?_, ?_⟩
  · have := (hsum.hasSum).div_const (∑' j, w j)
    rwa [div_self hS.ne'] at this
  · intro k
    have key : M.lamH * w k ≤ w (k + 1) ∧ w (k + 1) ≤ M.lam * w k := by
      simp only [hw]
      by_cases h1 : k + 1 ≤ n
      · rw [if_pos h1, if_pos (by omega), pow_succ]
        constructor
        · have := pow_nonneg hlam0.le k; nlinarith
        · linarith
      · by_cases h2 : k = n
        · subst h2
          rw [if_neg h1, if_pos le_rfl, show k + 1 - k - 1 = 0 by omega, pow_zero]
          constructor
          · nlinarith
          · have := pow_nonneg hlam0.le k
            nlinarith
        · rw [if_neg h1, if_neg (by omega)]
          have he : k + 1 - n - 1 = (k - n - 1) + 1 := by omega
          rw [he, pow_succ]
          have := pow_nonneg hlam0.le n
          have := pow_nonneg hH0.le (k - n - 1)
          have hp : 0 ≤ M.lam ^ n * M.lamH * M.lamH ^ (k - n - 1) := by positivity
          constructor
          · nlinarith
          · nlinarith
    constructor
    · rw [mul_div_assoc']; exact div_le_div_of_nonneg_right key.1 hS.le
    · rw [mul_div_assoc']; exact div_le_div_of_nonneg_right key.2 hS.le
  · have hg := summable_geom_mul_concave M.uL hdL haL M.lamH hH0.le hH1
    have h2 : Summable (fun k => w k * M.uL k) := by
      rw [← summable_nat_add_iff (n + 1)]
      have h3 := ((summable_nat_add_iff (n + 1)).mpr hg).mul_left
        (M.lam ^ n / M.lamH ^ n)
      refine h3.congr ?_
      intro j
      rw [hshift j]
      field_simp
      ring
    refine (h2.div_const (∑' j, w j)).congr ?_
    intro k; ring
  · have h2 : Summable (fun k => w k * M.uH k) := by
      rw [← summable_nat_add_iff (n + 1)]
      have h3 := ((summable_nat_add_iff (n + 1)).mpr hFin).mul_left
        (M.lam ^ n / M.lamH ^ n)
      refine h3.congr ?_
      intro j
      rw [hshift j]
      field_simp
      ring
    refine (h2.div_const (∑' j, w j)).congr ?_
    intro k; ring


/-- The counterexample utility `u(k) = 1 - 2k`. -/
noncomputable def u0 : ℕ → ℝ := fun k => 1 - 2 * (k : ℝ)

noncomputable def M0 (l : ℝ) : Model := ⟨l, 1/2, u0, u0⟩

lemma u0_strictAnti : StrictAnti u0 := by
  intro a b h
  have : (a : ℝ) < b := by exact_mod_cast h
  simp only [u0]; linarith

lemma u0_diff : Antitone (fun n => u0 n - u0 (n + 1)) := by
  intro a b _
  simp only [u0]; push_cast; linarith

lemma mfiOf_u0 : mfiOf u0 = 1 := by
  have hne : ({k | u0 k < 0} : Set ℕ).Nonempty := ⟨1, by norm_num [u0]⟩
  apply le_antisymm
  · exact Nat.sInf_le (by norm_num [u0])
  · by_contra h
    have h0 : mfiOf u0 = 0 := by omega
    have hm := Nat.sInf_mem hne
    have h0' : sInf ({k | u0 k < 0} : Set ℕ) = 0 := h0
    rw [h0'] at hm
    have : u0 0 < 0 := hm
    simp [u0] at this
    linarith

lemma standing_M0 (l : ℝ) (hl : l ∈ Set.Ioc (0 : ℝ) (1 - 1/2)) : (M0 l).Standing := by
  refine ⟨hl.1, by norm_num [M0], ?_, by simp [M0, u0], by simp [M0, u0],
    ⟨1, by norm_num [M0, u0]⟩, ⟨1, by norm_num [M0, u0]⟩,
    u0_strictAnti, u0_strictAnti, u0_diff⟩
  show l + 1/2 ≤ 1
  linarith [hl.2]

lemma hFin_u0 : Summable (fun n : ℕ => (1/2 : ℝ) ^ n * u0 n) :=
  summable_geom_mul_concave u0 u0_diff u0_strictAnti (1/2) (by norm_num) (by norm_num)

lemma tendsto_u0 : Filter.Tendsto u0 Filter.atTop Filter.atBot := by
  have h1 : Filter.Tendsto (fun k : ℕ => 2 * (k : ℝ)) Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop (by norm_num) tendsto_natCast_atTop_atTop
  have h2 := Filter.tendsto_neg_atTop_atBot.comp h1
  have h3 := Filter.tendsto_atBot_add_const_left Filter.atTop 1 h2
  refine h3.congr (fun k => ?_)
  simp [u0, Function.comp]; ring

/-- The explicit full-information policy at `λ_L = λ_H = 1/2`. -/
noncomputable def pstar : ℕ → ℝ := fun k => if k = 0 then 1/3 else (1/2) ^ (k - 1) / 3

lemma mfi_M0 : mfi (M0 (1/2)) = 1 := mfiOf_u0

lemma fi_M0 : fi (M0 (1/2)) = pstar := by
  have hlam : (M0 (1/2)).lam = 1 := by simp [Model.lam, M0]; norm_num
  have hH : (M0 (1/2)).lamH = 1/2 := rfl
  set w : ℕ → ℝ := fun k => if k ≤ 1 then 1 else 1 * (1/2) * (1/2) ^ (k - 1 - 1) with hw
  have hpol : fi (M0 (1/2)) = fun k => w k / ∑' j, w j := by
    funext k
    simp only [fi, thresholdPolicy, mfi_M0, Nat.cast_one, Nat.floor_one, Int.fract_one,
      zero_mul, add_zero, hlam, hH, one_pow, hw]
  have hsum : HasSum w 3 := by
    have hg := (hasSum_geometric_of_lt_one (r := (1/2 : ℝ)) (by norm_num) (by norm_num)).mul_left
      (1 * (1/2))
    have e : (fun n => w (n + 2)) = fun i => 1 * (1/2) * (1/2 : ℝ) ^ i := by
      funext n
      simp only [hw]
      rw [if_neg (by omega), show n + 2 - 1 - 1 = n by omega]
    have e2 : (3 : ℝ) - ∑ i ∈ Finset.range 2, w i = 1 * (1/2) * (1 - 1/2)⁻¹ := by
      simp [Finset.sum_range_succ, hw]; norm_num
    rw [← hasSum_nat_add_iff' 2, e, e2]
    exact hg
  rw [hpol, hsum.tsum_eq]
  funext k
  simp only [pstar, hw]
  rcases k with _ | _ | k
  · simp
  · simp
  · rw [if_neg (by omega), if_neg (by omega)]
    rw [show k + 1 + 1 - 1 - 1 = k by omega, show k + 1 + 1 - 1 = k + 1 by omega, pow_succ]
    ring

lemma WL_pstar : WL (M0 (1/2)) pstar = 1/6 := by
  unfold WL
  rw [tsum_eq_single 0]
  · simp [pstar, M0, u0]; norm_num
  · intro n hn
    simp only [pstar, M0]
    rw [if_neg (by omega), if_neg hn]
    rw [show n + 1 - 1 = (n - 1) + 1 by omega, pow_succ]
    ring

lemma unique_max (π : ℕ → ℝ) (hπ : π ∈ PiAP (M0 (1/2)))
    (hW : 1/6 ≤ WL (M0 (1/2)) π) : π = pstar := by
  obtain ⟨h0, h1, hr, hsL, -⟩ := hπ
  have hlam : (M0 (1/2)).lam = 1 := by simp [Model.lam, M0]; norm_num
  have hH : (M0 (1/2)).lamH = 1/2 := rfl
  have hx : ∀ n, 0 ≤ π (n + 1) - 1/2 * π n := by
    intro n; have := (hr n).1; rw [hH] at this; linarith
  have hup : π 1 ≤ π 0 := by have := (hr 0).2; rw [hlam] at this; linarith
  have hsL' : Summable (fun n => π n * u0 n) := hsL
  have hsπ : Summable π := h1.summable
  have hF : Summable (fun n => (π (n + 1) - 1/2 * π n) * u0 n) := by
    have a := (summable_nat_add_iff 1).mpr hsL'
    have b := (summable_nat_add_iff 1).mpr hsπ
    refine ((a.add (b.mul_left 2)).sub (hsL'.mul_left (1/2))).congr (fun n => ?_)
    simp only [u0]; push_cast; ring
  have hWL : WL (M0 (1/2)) π = ∑' n, (π (n + 1) - 1/2 * π n) * u0 n := rfl
  rw [hWL, hF.tsum_eq_zero_add] at hW
  have htail : ∑' n, (π (n + 1 + 1) - 1/2 * π (n + 1)) * u0 (n + 1) ≤ 0 := by
    apply tsum_nonpos
    intro n
    apply mul_nonpos_of_nonneg_of_nonpos (hx (n + 1))
    simp only [u0]; push_cast
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hu00 : u0 0 = 1 := by simp [u0]
  rw [hu00] at hW
  have hF0 : 1/6 ≤ π 1 - 1/2 * π 0 := by
    have : π (0 + 1) = π 1 := rfl
    linarith
  -- geometric lower bound
  have hgeo : ∀ n, (1/2 : ℝ) ^ n * π 1 ≤ π (n + 1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have := hx (n + 1)
      rw [pow_succ]; nlinarith
  have hs1 : HasSum (fun n => π (n + 1)) (1 - π 0) := by
    have := (hasSum_nat_add_iff' 1).mpr h1
    simpa using this
  have hg : HasSum (fun n => π (n + 1) - (1/2 : ℝ) ^ n * π 1) (1 - π 0 - 2 * π 1) := by
    have hgeom := (hasSum_geometric_of_lt_one (r := (1/2 : ℝ)) (by norm_num) (by norm_num)).mul_right
      (π 1)
    have := hs1.sub hgeom
    rw [show ((1:ℝ) - 1/2)⁻¹ = 2 by norm_num] at this
    exact this
  have hgnn : 0 ≤ 1 - π 0 - 2 * π 1 := hg.nonneg (fun n => by linarith [hgeo n])
  have hp1 : π 1 = 1/3 := by linarith
  have hp0 : π 0 = 1/3 := by linarith
  have hg0 : HasSum (fun n => π (n + 1) - (1/2 : ℝ) ^ n * π 1) 0 := by
    convert hg using 1; rw [hp0, hp1]; norm_num
  have hz := (hasSum_zero_iff_of_nonneg (fun n => by linarith [hgeo n])).mp hg0
  funext k
  rcases k with _ | k
  · simp [pstar, hp0]
  · have := congrFun hz k
    simp only [Pi.zero_apply] at this
    simp only [pstar, if_neg (Nat.succ_ne_zero k), Nat.add_sub_cancel]
    rw [hp1] at this
    linarith

end NP3Aux

open NeedPersuasion.FullInfo NP3Aux in
theorem solution : ¬ (∀ (lamH : ℝ) (uL uH : ℕ → ℝ)
    (hlamH : 0 < lamH ∧ lamH < 1)
    (hStand : ∀ l ∈ Set.Ioc (0 : ℝ) (1 - lamH), (⟨l, lamH, uL, uH⟩ : Model).Standing)
    (hFin : Summable (fun n : ℕ => lamH ^ n * uH n))
    (hu : uL (mfiOf uL - 1) ≠ 0),
    ∃ Λbar : ℝ, Λbar ∈ Set.Ioc (0 : ℝ) (1 - lamH) ∧
      0 < lowerBound lamH uL ∧ lowerBound lamH uL ≤ Λbar ∧
      -- Part 1
      (∀ l ∈ Set.Ioc (0 : ℝ) (1 - lamH),
        (l + lamH < 1 ∨
          (Filter.Tendsto uL Filter.atTop Filter.atBot ∧
            Filter.Tendsto uH Filter.atTop Filter.atBot)) →
        ((∃ π ∈ PiSM ⟨l, lamH, uL, uH⟩,
            Dominates ⟨l, lamH, uL, uH⟩ π (fi ⟨l, lamH, uL, uH⟩)) ↔ Λbar ≤ l)) ∧
      -- Part 2
      (∀ l ∈ Set.Ioc (0 : ℝ) (1 - lamH), Λbar ≤ l → l + lamH < 1 →
        let M : Model := ⟨l, lamH, uL, uH⟩
        M.uL (mfi M - 1) ≤ WL M (fi M) →
        M.uH (mfi M) ≤ WH M (fi M) →
        leaveValx M ((mfi M : ℝ) - 1) ≤ 0 →
        0 < WH M (fi M) →
        1 < betaL M ∧ 1 < betaH M ∧
          ∃ π ∈ PiSM M, betaL M * WL M (fi M) ≤ WL M π ∧ betaH M * WH M (fi M) ≤ WH M π)) := by
  intro H
  have hu : u0 (mfiOf u0 - 1) ≠ 0 := by rw [mfiOf_u0]; simp [u0]
  obtain ⟨Λ, hΛ, -, -, h1, -⟩ :=
    H (1/2) u0 u0 ⟨by norm_num, by norm_num⟩ (fun l hl => standing_M0 l hl) hFin_u0 hu
  have hl : (1/2 : ℝ) ∈ Set.Ioc (0 : ℝ) (1 - 1/2) := ⟨by norm_num, by norm_num⟩
  have hΛl : Λ ≤ 1/2 := by have := hΛ.2; linarith
  obtain ⟨π, hπ, hdom⟩ := (h1 (1/2) hl (Or.inr ⟨tendsto_u0, tendsto_u0⟩)).mpr hΛl
  have hdom' : Dominates (M0 (1/2)) π (fi (M0 (1/2))) := hdom
  have hπ' : π ∈ PiAP (M0 (1/2)) := hπ.1
  rw [fi_M0] at hdom'
  have hW : 1/6 ≤ WL (M0 (1/2)) π := by rw [← WL_pstar]; exact hdom'.1
  have hEq := unique_max π hπ' hW
  rw [hEq] at hdom'
  rcases hdom'.2.2 with h | h <;> exact lt_irrefl _ h
