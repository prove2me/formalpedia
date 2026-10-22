-- Prove2me | solution 1 for MCSustain.WinWin.proposition_3
-- status  : ACCEPTED   (disprove)
-- author  : @tianyipeng
-- created : 2026-10-21T20:07:21.402052+00:00
-- url     : https://prove2.me/submissions/9ca440ae-0caf-4df9-b490-238da88f84b1

import Mathlib
import Definitions.Def_MCSustain_WinWin_Model

namespace MCSustain.WinWin
namespace Cex

/-- Two-point newsvendor: the objective at any `q ≥ 0` is dominated by its value at `0`, `a` or `b`. -/
lemma nv_cases (α p c a b q : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (ha : 0 ≤ a) (hab : a ≤ b)
    (hc : 0 ≤ c) (hq : 0 ≤ q) :
    p * (α * min q b + (1 - α) * min q a) - c * q ≤ 0 ∨
    p * (α * min q b + (1 - α) * min q a) - c * q ≤ p * a - c * a ∨
    p * (α * min q b + (1 - α) * min q a) - c * q ≤ p * (α * b + (1 - α) * a) - c * b := by
  rcases le_total q a with h1 | h1
  · rw [min_eq_left h1, min_eq_left (h1.trans hab)]
    rcases le_total (p - c) 0 with h | h
    · left; nlinarith
    · right; left; nlinarith
  rcases le_total q b with h2 | h2
  · rw [min_eq_left h2, min_eq_right h1]
    rcases le_total (p * α - c) 0 with h | h
    · right; left; nlinarith
    · right; right; nlinarith
  · rw [min_eq_right h2, min_eq_right h1]
    right; right; nlinarith

lemma cbrt_eval (x y : ℝ) (hy : 0 ≤ y) (h : x = y ^ 3) : x ^ ((1 : ℝ) / 3) = y := by
  subst h
  rw [← Real.rpow_natCast, ← Real.rpow_mul hy]; norm_num

noncomputable def P0 : Params := ⟨1/2, 15, 1, 2, 1, 89/40, 343/16000, 1, 1, 0, 0, 0⟩

lemma P0_α : P0.α = 1/2 := rfl
lemma P0_mH : P0.mH = 15 := rfl
lemma P0_mL : P0.mL = 1 := rfl
lemma P0_t : P0.t = 2 := rfl
lemma P0_c : P0.c = 1 := rfl
lemma P0_r : P0.r = 89/40 := rfl
lemma P0_f : P0.f = 343/16000 := rfl
lemma P0_w : P0.w = 1 := rfl
lemma P0_ep : P0.ep = 1 := rfl
lemma P0_eu : P0.eu = 0 := rfl
lemma P0_ed : P0.ed = 0 := rfl
lemma P0_eo : P0.eo = 0 := rfl

lemma mu0 : P0.μ = 8 := by unfold Params.μ P0; norm_num
lemma be0 : P0.β = 8 := by unfold Params.β; rw [mu0]; unfold P0; norm_num

lemma standing0 : P0.Standing := by
  unfold Params.Standing Params.Es Params.El
  rw [be0]; unfold P0; norm_num

/-- MP profit bound, three branches. -/
lemma profit_branches (P : Params) (hα0 : 0 < P.α) (hα1 : P.α < 1) (hmL : 0 ≤ P.mL)
    (hmH : P.mL ≤ P.mH) (hc : 0 ≤ P.c) (x : MPDec) (hx : x.Feasible) :
    profitMP P x ≤ - (P.f * x.n ^ 2) ∨
    profitMP P x ≤ x.n * (pMP P x.lam * (P.mL * x.lam) - P.c * (P.mL * x.lam)) - P.f * x.n ^ 2 ∨
    profitMP P x ≤ x.n * (pMP P x.lam * (P.α * (P.mH * x.lam) + (1 - P.α) * (P.mL * x.lam))
        - P.c * (P.mH * x.lam)) - P.f * x.n ^ 2 := by
  obtain ⟨hn, hl0, -, -, hq⟩ := hx
  have key := nv_cases P.α (pMP P x.lam) P.c (P.mL * x.lam) (P.mH * x.lam) x.q hα0 hα1
    (by positivity) (by nlinarith) hc hq
  have e : profitMP P x = x.n * (pMP P x.lam * (P.α * min x.q (P.mH * x.lam) +
      (1 - P.α) * min x.q (P.mL * x.lam)) - P.c * x.q) - P.f * x.n ^ 2 := by
    unfold profitMP sales E; ring
  rw [e]
  rcases key with h | h | h
  · left; nlinarith [mul_le_mul_of_nonneg_left h hn]
  · right; left; nlinarith [mul_le_mul_of_nonneg_left h hn]
  · right; right; nlinarith [mul_le_mul_of_nonneg_left h hn]

lemma hyb_le (P : Params) (hP : P.Standing) (y : HybDec) (hy : y.Feasible P) :
    profitHyb P y ≤ profitMP P y.toMPDec + (P.r - P.w - P.c) * P.μ * (1 - y.n * y.lam) := by
  obtain ⟨⟨hn, hl0, hl1, hnl, hq⟩, hmc, hsum, hp⟩ := hy
  have hmu0 : 0 < P.μ := by
    unfold Params.μ; have := hP.1; have := hP.2.1; have := hP.2.2.1; have := hP.2.2.2.1; nlinarith
  have hw := hP.2.2.2.2.2.2.2.2.2.2.1
  unfold profitHyb
  rcases hmc.lt_or_eq with h | h
  · have := hp h
    have h1 : (y.pMC - P.c) * y.lamMC ≤ (P.r - P.w - P.c) * y.lamMC :=
      mul_le_mul_of_nonneg_right (by linarith) hmc
    have h2 : (P.r - P.w - P.c) * y.lamMC ≤ (P.r - P.w - P.c) * (1 - y.n * y.lam) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    nlinarith
  · rw [← h]
    have : 0 ≤ (P.r - P.w - P.c) * (1 - y.n * y.lam) := mul_nonneg (by linarith) (by linarith)
    nlinarith

lemma Lc0 : Lc P0 = ⟨20/7, 7/20, 7/20⟩ := by
  have h : (P0.t * P0.mL / (4 * P0.f)) ^ ((1 : ℝ) / 3) = 20 / 7 := by
    apply cbrt_eval _ _ (by norm_num); unfold P0; norm_num
  unfold Lc; rw [h]; unfold P0; norm_num

lemma lamHp0 : lamHp P0 = 1/16 := by unfold lamHp; rw [be0]; unfold P0; norm_num

lemma Hup0 : Hup P0 = ⟨⟨250/343, 1/16, 15/16⟩, 49/40, 1 - 250/343 * (1/16)⟩ := by
  unfold Hup; rw [lamHp0, mu0]; unfold P0; norm_num

lemma polyL (n l : ℝ) (hn : 0 ≤ n) (hl : 0 ≤ l) (hnl : n * l ≤ 1) :
    n * (l * (49/40) - l ^ 2) - 343/16000 * n ^ 2 ≤ 7/10 := by
  rcases le_total n (80/49) with h | h
  · nlinarith [mul_nonneg hn (sq_nonneg (l - 49/80))]
  · have hnpos : 0 < n := by linarith
    have h1 : 0 ≤ (1 - n * l) * (49/40 * n - 1 - n * l) :=
      mul_nonneg (by linarith) (by nlinarith)
    have h2 : 0 ≤ (n - 20/7) ^ 2 * (n + 40/7) := mul_nonneg (sq_nonneg _) (by linarith)
    have : n * (n * (l * (49/40) - l ^ 2) - 343/16000 * n ^ 2) ≤ n * (7/10) := by nlinarith
    exact le_of_mul_le_mul_left this hnpos

lemma polyH (n l : ℝ) (hn : 0 ≤ n) :
    n * (l * (14/5) - 8 * l ^ 2) - 343/16000 * n ^ 2 ≤ 7/10 := by
  nlinarith [mul_nonneg hn (sq_nonneg (l - 7/40)), sq_nonneg (n - 40/7)]

lemma polyHp (n l : ℝ) (hn : 0 ≤ n) :
    n * (l - 8 * l ^ 2) - 343/16000 * n ^ 2 ≤ 125/10976 := by
  nlinarith [mul_nonneg hn (sq_nonneg (l - 1/16)), sq_nonneg (n - 250/343)]

lemma optLc : IsOptMP P0 (Lc P0) := by
  rw [Lc0]
  refine ⟨by unfold MPDec.Feasible; norm_num, ?_⟩
  intro x hx
  have hv : profitMP P0 ⟨20/7, 7/20, 7/20⟩ = 7/10 := by
    unfold profitMP sales E pMP P0; norm_num
  rw [hv]
  have hx' := hx
  obtain ⟨hn, hl0, hl1, hnl, hq⟩ := hx'
  rcases profit_branches P0 (by unfold P0; norm_num) (by unfold P0; norm_num)
    (by unfold P0; norm_num) (by unfold P0; norm_num) (by unfold P0; norm_num) x hx with h | h | h
  · have : 0 ≤ P0.f * x.n ^ 2 := by unfold P0; positivity
    linarith
  · simp only [pMP, P0_α, P0_mH, P0_mL, P0_t, P0_c, P0_r, P0_f, P0_w] at h
    nlinarith [polyL x.n x.lam hn hl0 hnl]
  · simp only [pMP, P0_α, P0_mH, P0_mL, P0_t, P0_c, P0_r, P0_f, P0_w] at h
    nlinarith [polyH x.n x.lam hn]

lemma optHup : IsOptHyb P0 (Hup P0) := by
  rw [Hup0]
  refine ⟨by unfold HybDec.Feasible MPDec.Feasible P0; norm_num, ?_⟩
  intro y hy
  have hv : profitHyb P0 ⟨⟨250/343, 1/16, 15/16⟩, 49/40, 1 - 250/343 * (1/16)⟩ =
      9/5 + 125/10976 := by
    unfold profitHyb profitMP sales E pMP; rw [mu0]; unfold P0; norm_num
  rw [hv]
  have hb := hyb_le P0 standing0 y hy
  rw [mu0] at hb
  have hy' := hy.1
  obtain ⟨hn, hl0, hl1, hnl, hq⟩ := hy.1
  rcases profit_branches P0 (by unfold P0; norm_num) (by unfold P0; norm_num)
    (by unfold P0; norm_num) (by unfold P0; norm_num) (by unfold P0; norm_num) _ hy' with h | h | h
  · simp only [P0_α, P0_mH, P0_mL, P0_t, P0_c, P0_r, P0_f, P0_w] at h hb
    nlinarith [mul_nonneg hn hl0]
  · simp only [pMP, P0_α, P0_mH, P0_mL, P0_t, P0_c, P0_r, P0_f, P0_w] at h hb
    nlinarith [mul_nonneg hn hl0, mul_nonneg (mul_nonneg hn hl0) hl0]
  · simp only [pMP, P0_α, P0_mH, P0_mL, P0_t, P0_c, P0_r, P0_f, P0_w] at h hb
    nlinarith [polyHp y.n y.lam hn]

lemma impLc : impactMP P0 (Lc P0) = 1 := by
  rw [Lc0]; unfold impactMP sales leftover E Params.Es Params.El P0; norm_num

lemma impHup : impactHyb P0 (Hup P0) = 8 + 7 * (250/343 * (1/16)) := by
  rw [Hup0]; unfold impactHyb impactMP sales leftover E Params.Es Params.El; rw [mu0]
  unfold P0; norm_num

lemma not_winwin : ¬ WinWin P0 := by
  intro h
  have := (h.2.2 _ _ optLc optHup).2
  rw [impLc, impHup] at this
  norm_num at this


lemma rp (x : ℝ) (k : ℕ) (h : x = 2 ^ 3) : x ^ ((k : ℝ) / 3) = 2 ^ k := by
  subst h
  rw [← Real.rpow_natCast 2 3, ← Real.rpow_mul (by norm_num)]
  rw [show ((3 : ℕ) : ℝ) * ((k : ℝ) / 3) = (k : ℝ) by push_cast; ring, Real.rpow_natCast]

lemma b13 : P0.β ^ ((1 : ℝ) / 3) = 2 := by
  have := rp P0.β 1 (by rw [be0]; norm_num); simpa using this
lemma b23 : P0.β ^ ((2 : ℝ) / 3) = 4 := by
  have := rp P0.β 2 (by rw [be0]; norm_num); norm_num at this; exact this
lemma b43 : P0.β ^ ((4 : ℝ) / 3) = 16 := by
  have := rp P0.β 4 (by rw [be0]; norm_num); norm_num at this; exact this

lemma k1_0 : κ1 P0 = 89/40 := by
  unfold κ1; rw [b13, b23, b43, be0, P0_α]; norm_num

lemma k2_0 : 89/40 < κ2 P0 := by
  unfold κ2; rw [be0, P0_α]
  have hs : Real.sqrt 8 < 3 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hs0 : 0 < Real.sqrt 8 := by positivity
  rw [lt_div_iff₀ (by positivity)]
  nlinarith

lemma fH0 : fH P0 = 343/16000 := by
  unfold fH lamH; rw [be0, mu0]; simp only [P0_α, P0_t, P0_c, P0_r]; norm_num

lemma fHp0 : fHp P0 = 1/1024 := by
  unfold fHp; rw [lamHp0, mu0, P0_t]; norm_num

lemma rhs0 : (κ2 P0 ≤ P0.r / P0.c ∧
          ((fH P0 < P0.f ∧ R P0 < P0.El / P0.Es) ∨ (P0.f ≤ fH P0 ∧ fHp P0 < P0.f))) ∨
      (κ1 P0 ≤ P0.r / P0.c ∧ P0.r / P0.c < κ2 P0 ∧
          ((P0.f < fcu P0 ∧ fH P0 < P0.f ∧ R P0 < P0.El / P0.Es) ∨
            (P0.f ≤ fH P0 ∧ fHp P0 < P0.f))) ∨
      (P0.r / P0.c < κ1 P0 ∧ P0.f < fc P0 ∧ fHp P0 < P0.f ∧ P0.w ≤ w2 P0) := by
  right; left
  have hrc : P0.r / P0.c = 89/40 := by rw [P0_r, P0_c]; norm_num
  refine ⟨by rw [k1_0, hrc], by rw [hrc]; exact k2_0, Or.inr ⟨?_, ?_⟩⟩
  · rw [fH0, P0_f]
  · rw [fHp0, P0_f]; norm_num

end Cex
end MCSustain.WinWin

open MCSustain.WinWin in
theorem solution : ¬ (∀ (P : Params) (hP : P.Standing),
    WinWin P ↔
      (κ2 P ≤ P.r / P.c ∧
          ((fH P < P.f ∧ R P < P.El / P.Es) ∨ (P.f ≤ fH P ∧ fHp P < P.f))) ∨
      (κ1 P ≤ P.r / P.c ∧ P.r / P.c < κ2 P ∧
          ((P.f < fcu P ∧ fH P < P.f ∧ R P < P.El / P.Es) ∨ (P.f ≤ fH P ∧ fHp P < P.f))) ∨
      (P.r / P.c < κ1 P ∧ P.f < fc P ∧ fHp P < P.f ∧ P.w ≤ w2 P)) := by
  intro h
  exact Cex.not_winwin ((h Cex.P0 Cex.standing0).2 Cex.rhs0)
