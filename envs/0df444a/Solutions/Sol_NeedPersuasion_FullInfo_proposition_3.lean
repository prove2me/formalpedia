-- Prove2me | solution 1 for NeedPersuasion.FullInfo.proposition_3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T23:22:27.987193+00:00
-- url     : https://prove2.me/submissions/eea00840-788b-4d34-9681-5fe2cfd0b851
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_NeedPersuasion_FullInfo_Model
import Definitions.Def_NeedPersuasion_FullInfo_Constants
import Theorems.Thm_NeedPersuasion_FullInfo_theorem_4
import Theorems.Thm_NeedPersuasion_FullInfo_f_equivalence
import Theorems.Thm_NeedPersuasion_FullInfo_wl_identity
import Theorems.Thm_NeedPersuasion_FullInfo_wh_inequality
import Theorems.Thm_NeedPersuasion_FullInfo_leave_fi_neg

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

/-- The function `f(·, λ_H)` as a function of `λ_L` alone. -/
noncomputable def Fl (lamH : ℝ) (uL : ℕ → ℝ) (l : ℝ) : ℝ :=
  l * uL 0 - l * ∑ k ∈ Finset.Ico 1 (mfiOf uL), (lamH + l) ^ k * (uL (k - 1) - uL k) -
    (1 - lamH) * uL (mfiOf uL - 1)

lemma fF_eq (l lamH : ℝ) (uL uH : ℕ → ℝ) :
    fF ⟨l, lamH, uL, uH⟩ = Fl lamH uL l := rfl

lemma telescope (uL : ℕ → ℝ) (m : ℕ) (hm : 1 ≤ m) :
    ∑ k ∈ Finset.Ico 1 m, (uL (k - 1) - uL k) = uL 0 - uL (m - 1) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel]
  have := Finset.sum_range_sub' (fun i => uL i) n
  rw [← this]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp [Nat.add_comm 1 i]

lemma phi_convex (lamH : ℝ) (hH : 0 ≤ lamH) (k : ℕ) :
    ConvexOn ℝ (Set.Ici (0 : ℝ)) (fun l : ℝ => l * (lamH + l) ^ k) := by
  have h1 : ConvexOn ℝ (Set.Ici (0 : ℝ)) (fun l : ℝ => l) := convexOn_id (convex_Ici 0)
  have h2 : ConvexOn ℝ (Set.Ici (0 : ℝ)) (fun l : ℝ => lamH + l) :=
    (convexOn_const lamH (convex_Ici 0)).add h1
  have h3 : ConvexOn ℝ (Set.Ici (0 : ℝ)) ((fun l : ℝ => lamH + l) ^ k) :=
    h2.pow (fun x hx => by simp only [Set.mem_Ici] at hx; linarith) k
  have := h1.mul h3 (fun x hx => hx) (fun x hx => by
      simp only [Set.mem_Ici] at hx; simp only [Pi.pow_apply]; positivity)
    (MonotoneOn.monovaryOn (fun a _ b _ h => h) (fun a ha b hb h => by
      simp only [Set.mem_Ici] at ha hb
      simp only [Pi.pow_apply]
      exact pow_le_pow_left₀ (by linarith) (by linarith) k))
  exact this

lemma Fl_concave (lamH : ℝ) (hH : 0 ≤ lamH) (uL : ℕ → ℝ) (hu : StrictAnti uL)
    (a b t : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t * Fl lamH uL a + (1 - t) * Fl lamH uL b ≤ Fl lamH uL (t * a + (1 - t) * b) := by
  unfold Fl
  have key : ∀ k ∈ Finset.Ico 1 (mfiOf uL),
      (t * a + (1 - t) * b) * (lamH + (t * a + (1 - t) * b)) ^ k * (uL (k - 1) - uL k) ≤
        t * (a * (lamH + a) ^ k * (uL (k - 1) - uL k)) +
          (1 - t) * (b * (lamH + b) ^ k * (uL (k - 1) - uL k)) := by
    intro k hk
    have hd : 0 ≤ uL (k - 1) - uL k := by
      have := hu (show k - 1 < k by simp at hk; omega); linarith
    have hc := (phi_convex lamH hH k).2 (Set.mem_Ici.mpr ha) (Set.mem_Ici.mpr hb) ht0
      (by linarith : 0 ≤ 1 - t) (by ring)
    simp only [smul_eq_mul] at hc
    have := mul_le_mul_of_nonneg_right hc hd
    linarith
  have hs := Finset.sum_le_sum key
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hs
  have e1 : ∀ x : ℝ, x * ∑ k ∈ Finset.Ico 1 (mfiOf uL), (lamH + x) ^ k * (uL (k - 1) - uL k) =
      ∑ k ∈ Finset.Ico 1 (mfiOf uL), x * (lamH + x) ^ k * (uL (k - 1) - uL k) := by
    intro x; rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun k _ => by ring)
  rw [e1, e1, e1]
  nlinarith [hs]

end NP3Aux

open NeedPersuasion.FullInfo NP3Aux in
theorem solution (lamH : ℝ) (uL uH : ℕ → ℝ)
    (hlamH : 0 < lamH ∧ lamH < 1)
    (hStand : ∀ l ∈ Set.Ioc (0 : ℝ) (1 - lamH), (⟨l, lamH, uL, uH⟩ : Model).Standing)
    (hFin : Summable (fun n : ℕ => lamH ^ n * uH n))
    (hu : uL (mfiOf uL - 1) ≠ 0) :
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
          ∃ π ∈ PiSM M, betaL M * WL M (fi M) ≤ WL M π ∧ betaH M * WH M (fi M) ≤ WH M π) := by
  obtain ⟨hH0, hH1⟩ := hlamH
  set T : ℝ := 1 - lamH with hT
  have hT0 : 0 < T := by linarith
  have hTmem : T ∈ Set.Ioc (0 : ℝ) T := ⟨hT0, le_rfl⟩
  -- Facts about `u_L` from the standing assumptions (at `λ_L = T`).
  obtain ⟨-, -, -, hu0, -, ⟨k0, hk0⟩, -, haL, -, -⟩ := hStand T hTmem
  set m := mfiOf uL with hmdef
  have hne : ({k | uL k < 0} : Set ℕ).Nonempty := ⟨k0, hk0⟩
  have hm1 : 1 ≤ m := by
    by_contra h
    have h0 : m = 0 := by omega
    have hmem := Nat.sInf_mem hne
    have hm0 : sInf ({k | uL k < 0} : Set ℕ) = 0 := h0
    rw [hm0] at hmem
    have : uL 0 < 0 := hmem
    linarith
  have hc0 : 0 ≤ uL (m - 1) := by
    have := Nat.notMem_of_lt_sInf (s := {k | uL k < 0}) (m := m - 1)
      (by show m - 1 < m; omega)
    simp only [Set.mem_setOf_eq, not_lt] at this
    exact this
  have hc : 0 < uL (m - 1) := lt_of_le_of_ne hc0 (Ne.symm hu)
  have hdk : ∀ k ∈ Finset.Ico 1 m, 0 ≤ uL (k - 1) - uL k := by
    intro k hk
    have := haL (show k - 1 < k by simp at hk; omega); linarith
  have htel := telescope uL m hm1
  -- The denominator `G0` of the lower bound.
  set G0 : ℝ := uL 0 - ∑ k ∈ Finset.Ico 1 m, lamH ^ k * (uL (k - 1) - uL k) with hG0
  have hG0c : uL (m - 1) ≤ G0 := by
    have : ∑ k ∈ Finset.Ico 1 m, lamH ^ k * (uL (k - 1) - uL k) ≤
        ∑ k ∈ Finset.Ico 1 m, (uL (k - 1) - uL k) := by
      refine Finset.sum_le_sum (fun k hk => ?_)
      have := hdk k hk
      have : lamH ^ k ≤ 1 := pow_le_one₀ hH0.le hH1.le
      nlinarith
    rw [hG0]; linarith
  have hG0pos : 0 < G0 := lt_of_lt_of_le hc hG0c
  have hlb : lowerBound lamH uL = T * (uL (m - 1) / G0) := rfl
  have hlbpos : 0 < lowerBound lamH uL := by rw [hlb]; positivity
  -- F(T) = 0
  have hFT : Fl lamH uL T = 0 := by
    unfold Fl
    rw [show lamH + T = 1 by rw [hT]; ring]
    simp only [one_pow, one_mul]
    rw [← hmdef, htel]; ring
  -- F(l) ≥ 0 implies l ≥ lowerBound
  have hFlb : ∀ l, 0 ≤ l → 0 ≤ Fl lamH uL l → lowerBound lamH uL ≤ l := by
    intro l hl hF
    unfold Fl at hF
    rw [← hmdef] at hF
    have : ∑ k ∈ Finset.Ico 1 m, lamH ^ k * (uL (k - 1) - uL k) ≤
        ∑ k ∈ Finset.Ico 1 m, (lamH + l) ^ k * (uL (k - 1) - uL k) := by
      refine Finset.sum_le_sum (fun k hk => ?_)
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hH0.le (by linarith) k) (hdk k hk)
    have h1 : T * uL (m - 1) ≤ l * G0 := by
      rw [hG0]; nlinarith
    rw [hlb, ← mul_div_assoc, div_le_iff₀ hG0pos]; exact h1
  -- The threshold set and its infimum.
  set S : Set ℝ := {l | l ∈ Set.Icc (lowerBound lamH uL) T ∧ 0 ≤ Fl lamH uL l} with hSdef
  have hTS : T ∈ S := ⟨⟨hFlb T hT0.le (by rw [hFT]), le_rfl⟩, by rw [hFT]⟩
  have hcont : Continuous (Fl lamH uL) := by unfold Fl; fun_prop
  have hSclosed : IsClosed S :=
    isClosed_Icc.inter (isClosed_le continuous_const hcont)
  have hSbdd : BddBelow S := ⟨lowerBound lamH uL, fun x hx => hx.1.1⟩
  set Λ := sInf S with hΛ
  have hΛS : Λ ∈ S := hSclosed.csInf_mem ⟨T, hTS⟩ hSbdd
  have hΛT : Λ ≤ T := csInf_le hSbdd hTS
  -- Characterization: for l ∈ (0, T], 0 ≤ F l ↔ Λ ≤ l.
  have hchar : ∀ l ∈ Set.Ioc (0 : ℝ) T, (0 ≤ Fl lamH uL l ↔ Λ ≤ l) := by
    intro l hl
    constructor
    · intro hF
      exact csInf_le hSbdd ⟨⟨hFlb l hl.1.le hF, hl.2⟩, hF⟩
    · intro hle
      have hΛ0 : 0 ≤ Λ := le_trans hlbpos.le hΛS.1.1
      rcases eq_or_lt_of_le hΛT with h | h
      · have : l = T := le_antisymm hl.2 (h ▸ hle)
        rw [this, hFT]
      · set t := (T - l) / (T - Λ) with ht
        have hTL : 0 < T - Λ := by linarith
        have ht0 : 0 ≤ t := div_nonneg (by linarith [hl.2]) hTL.le
        have ht1 : t ≤ 1 := by rw [ht, div_le_one hTL]; linarith
        have hl' : t * Λ + (1 - t) * T = l := by
          rw [ht]; field_simp; ring
        have := Fl_concave lamH hH0.le uL haL Λ T t hΛ0 hT0.le ht0 ht1
        rw [hl', hFT] at this
        have := hΛS.2
        nlinarith
  refine ⟨Λ, ⟨lt_of_lt_of_le hlbpos hΛS.1.1, hΛT⟩, hlbpos, hΛS.1.1, ?_, ?_⟩
  · -- Part 1
    intro l hl hExist
    have hS := hStand l hl
    have h4 := theorem_4 ⟨l, lamH, uL, uH⟩ hS hH0 hFin hExist
    have hf := f_equivalence ⟨l, lamH, uL, uH⟩ hS
    rw [fF_eq] at hf
    rw [← hchar l hl]
    obtain ⟨hx, hiff⟩ := h4
    rw [xor_iff_iff_not] at hx
    constructor
    · intro hD
      by_contra hneg
      exact hx.mp (hiff.mpr (hf.mpr (lt_of_not_ge hneg))) hD
    · intro hF
      by_contra hneg
      have hPE : ParetoEfficientIn ⟨l, lamH, uL, uH⟩ (PiAP ⟨l, lamH, uL, uH⟩)
          (fi ⟨l, lamH, uL, uH⟩) := hx.mpr hneg
      have := hf.mp (hiff.mp hPE)
      linarith
  · -- Part 2
    intro l hl _hΛl hlt M hWL hWH hLv _hWHpos
    have hS : M.Standing := hStand l hl
    have hL0 : 0 < M.lamL := hl.1
    have hlamM : M.lam = l + lamH := rfl
    have hlt' : M.lam < 1 := by rw [hlamM]; exact hlt
    have hmM : mfi M = m := rfl
    have hlam0 : 0 < M.lam := by rw [hlamM]; linarith [hl.1]
    have hpow : M.lam ^ (mfi M - 1) ≤ 1 := pow_le_one₀ hlam0.le hlt'.le
    have hpow0 : 0 < M.lam ^ (mfi M - 1) := pow_pos hlam0 _
    have hD : 0 < 1 - M.lamH - M.lamL * M.lam ^ (mfi M - 1) := by
      have : M.lamL * M.lam ^ (mfi M - 1) ≤ M.lamL := by nlinarith
      have h2 : M.lamL + M.lamH < 1 := hlt
      linarith
    have hX : 0 < (1 - M.lam) * M.lamL * M.lam ^ (mfi M - 1) :=
      mul_pos (mul_pos (by linarith) hL0) hpow0
    have hMH : M.lamH = lamH := rfl
    have hbL : 1 < betaL M := by
      unfold betaL
      have : 0 < M.lamH * (1 - M.lam) * M.lamL * M.lam ^ (mfi M - 1) /
          (1 - M.lamH - M.lamL * M.lam ^ (mfi M - 1)) := by
        apply div_pos _ hD
        have := mul_pos (show 0 < M.lamH from hH0) hX
        linarith [show M.lamH * (1 - M.lam) * M.lamL * M.lam ^ (mfi M - 1) =
          M.lamH * ((1 - M.lam) * M.lamL * M.lam ^ (mfi M - 1)) by ring]
      linarith
    have hbH : 1 < betaH M := by
      unfold betaH
      have : 0 < (1 - M.lamH) * (1 - M.lam) * M.lamL * M.lam ^ (mfi M - 1) /
          (1 - M.lamH - M.lamL * M.lam ^ (mfi M - 1)) := by
        apply div_pos _ hD
        have := mul_pos (show 0 < 1 - M.lamH by rw [hMH]; linarith) hX
        linarith [show (1 - M.lamH) * (1 - M.lam) * M.lamL * M.lam ^ (mfi M - 1) =
          (1 - M.lamH) * ((1 - M.lam) * M.lamL * M.lam ^ (mfi M - 1)) by ring]
      linarith
    have hm1M : 1 ≤ mfi M := hm1
    have hwl := wl_identity M hS hlt' (mfi M) hm1M le_rfl
    have hwh := wh_inequality M hS hlt' hFin (mfi M) hm1M le_rfl
    have hfi := leave_fi_neg M hS hFin
    have hWL0 : 0 ≤ WL M (fi M) := hfi.1.2.1
    have hWLfi : WLx M (mfi M) = WL M (fi M) := rfl
    have hWHfi : WHx M (mfi M) = WH M (fi M) := rfl
    rw [hWLfi] at hwl
    rw [hWHfi] at hwh
    set π := thresholdPolicy M ((mfi M : ℝ) - 1) with hπ
    have hWLπ : WLx M ((mfi M : ℝ) - 1) = WL M π := rfl
    have hWHπ : WHx M ((mfi M : ℝ) - 1) = WH M π := rfl
    rw [hWLπ] at hwl
    rw [hWHπ] at hwh
    set D := 1 - M.lamH - M.lamL * M.lam ^ (mfi M - 1) with hDdef
    set X := (1 - M.lam) * M.lamL * M.lam ^ (mfi M - 1) with hXdef
    have hY : 0 ≤ (1 - M.lamH) * (1 - M.lam) * M.lamL * M.lam ^ (mfi M - 1) / D := by
      apply div_nonneg _ hD.le
      have := mul_pos (show 0 < 1 - M.lamH by rw [hMH]; linarith) hX
      linarith [show (1 - M.lamH) * (1 - M.lam) * M.lamL * M.lam ^ (mfi M - 1) =
          (1 - M.lamH) * X by rw [hXdef]; ring]
    have hY' : 0 ≤ M.lamH * (1 - M.lam) * M.lamL * M.lam ^ (mfi M - 1) / D := by
      apply div_nonneg _ hD.le
      have := mul_pos (show 0 < M.lamH from hH0) hX
      linarith [show M.lamH * (1 - M.lam) * M.lamL * M.lam ^ (mfi M - 1) =
          M.lamH * X by rw [hXdef]; ring]
    have hLbound : betaL M * WL M (fi M) ≤ WL M π := by
      rw [hwl]
      have e : betaL M * WL M (fi M) = (1 + X / D) * WL M (fi M) -
          (1 - M.lamH) * (1 - M.lam) * M.lamL * M.lam ^ (mfi M - 1) / D * WL M (fi M) := by
        unfold betaL; rw [← hDdef, hXdef]; ring
      rw [e]
      exact sub_le_sub_left (mul_le_mul_of_nonneg_left hWL hY) _
    have hHbound : betaH M * WH M (fi M) ≤ WH M π := by
      refine le_trans ?_ hwh
      have e : betaH M * WH M (fi M) = (1 + X / D) * WH M (fi M) -
          M.lamH * (1 - M.lam) * M.lamL * M.lam ^ (mfi M - 1) / D * WH M (fi M) := by
        unfold betaH; rw [← hDdef, hXdef]; ring
      rw [e]
      exact sub_le_sub_left (mul_le_mul_of_nonneg_left hWH hY') _
    refine ⟨hbL, hbH, π, ⟨?_, ?_, hLv⟩, hLbound, hHbound⟩
    · have hcast : ((mfi M : ℝ) - 1) = ((mfi M - 1 : ℕ) : ℝ) := by
        rw [Nat.cast_sub hm1M]; simp
      rw [hπ, hcast]
      exact threshold_mem_PiAP M hS hH0 hH1 hFin (mfi M - 1)
    · show 0 ≤ WL M π
      have : 0 ≤ betaL M * WL M (fi M) := mul_nonneg (by linarith) hWL0
      linarith
